import Solcore.Test.SourceCoreEvidenceDirectSource
import Solcore.Test.SourceCoreCapturedLocalSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreEvidenceScoped
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreEvidenceDirect.Read
abbrev TypedNode := Tests.SourceCoreEvidenceDirect.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
abbrev ChooseShape := Tests.SourceCoreEvidenceDirect.ChooseShape
abbrev DirectCall := Tests.SourceCoreEvidenceDirect.DirectCall
abbrev mark := Tests.SourceCoreEvidenceDirect.mark
abbrev observeChoose := Tests.SourceCoreEvidenceDirect.observeChoose
abbrev observeDirect := Tests.SourceCoreEvidenceDirect.observeDirect
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode

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

structure RootCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId)
    (firstType secondType : TypeSystem.Ty) (firstArgument secondArgument flagArgument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function (.product firstType (.product secondType .bool)) firstType)
  value : CallNode source firstType
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)
  different : firstParameter ≠ secondParameter
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)],
    .function (.product (.parameter firstParameter) (.product (.parameter secondParameter) .bool)) (.parameter firstParameter)⟩
  inputs : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter, .bool]
  returns : signature.returnTypes = [.parameter firstParameter]
  exact : instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)],
    .function (.product firstType (.product secondType .bool)) firstType, [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩

theorem RootCall.typed {source signature firstParameter secondParameter firstType secondType firstArgument secondArgument flagArgument trait}
    (call : RootCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument flagArgument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context firstType) (secondFormed : TypeAdmissible context secondType)
    (firstTyped : ExpressionHasType source context firstArgument firstType)
    (secondTyped : ExpressionHasType source context secondArgument secondType)
    (flagTyped : ExpressionHasType source context flagArgument .bool)
    (required : RequirementProves context call.requirement (mark trait firstType)) :
    ExpressionHasType source context call.value.node.id firstType := by
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
    · simp [call.scheme, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.scheme, mark, Tests.SourceCoreEvidenceDirect.mark, ProgramPredicate.applyParameters, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
  have application : DeclarationApplicationValid context call.instantiation [firstType, secondType, .bool] firstType [mark trait firstType] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.cons flagTyped (.nil _)))))
      call.value.raw firstFormed (call.value.type.symm ▸ firstFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  flagRead : Read function.typedBody flag .bool
  call : RootCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id flagRead.node.id trait
  statement : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = mark trait firstType
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = firstType

def RootShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.flagRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType, .bool])
    (returns : signature.returnTypes = [firstType]) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let facts : StatementFacts := {type := firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
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
        have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
        have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
        have currentLedger := ledger.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.2.1.trans (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1))
          (flagExtended.context_fields.2.2.2.2.trans (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2))
        have rowMember : shape.solved ∈ lexical.solvedRequirements := by
          rw [flagExtended.context_fields.2.2.2.2, secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
          exact shape.solvedMember
        have required : RequirementProves lexical shape.call.requirement (mark trait firstType) :=
          ⟨shape.solved, ⟨rowMember, shape.solvedId⟩, shape.solvedPredicate,
            currentLedger.ordinary_valid rowMember (by simp [shape.noTemplates])⟩
        have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_self))
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_scheme_requirements_self))
        have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
          (by cases flagExtended; exact .tail shape.flagSecond secondExtended.local_self)
          (by cases flagExtended; exact .tail shape.flagSecond secondExtended.local_scheme_requirements_self)
        have flagTyped := shape.flagRead.typed flagScheme shape.flagRequirements
          ⟨firstFormed.1, .builtin .bool⟩ flagExtended.local_self flagExtended.local_scheme_requirements_self
        have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped flagTyped required
        exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
          shape.statementForm callTyped shape.statementType)⟩
def observeRootCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty)
    (firstArgument secondArgument flagArgument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (RootCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument flagArgument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product firstType (.product secondType .bool)) firstType)
  let value ← observeCallNode source value firstType
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)) "generic direct form"
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "generic direct different"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [mark trait (.parameter firstParameter)], .function (.product (.parameter firstParameter) (.product (.parameter secondParameter) .bool)) (.parameter firstParameter)⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter, .bool]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter firstParameter]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)], .function (.product firstType (.product secondType .bool)) firstType, [mark trait firstType], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, different, scheme, inputs, returns, exact}
def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RootShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression readFlag, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag readFlag .bool
  let call ← observeRootCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id flagRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "flagSecond"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = mark trait firstType) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
    let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flagScheme"
    let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "flagRequirements"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = firstType) "generic root statementType"
    return {flag, flagRead, flagFirst, flagSecond, flagScheme, flagRequirements, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")


structure Required (function : CheckedFunction) (id : RequirementId) (predicate : ProgramPredicate) where
  row : SolvedRequirement
  member : row ∈ function.solvedRequirements
  identity : row.id = id
  predicateEq : row.predicate = predicate

theorem Required.proves {function id predicate} (required : Required function id predicate)
    {context : SourceSemantics.Context}
    (ledger : ScopedRequirementLedgerWellFormed context function.typedBody)
    (same : context.solvedRequirements = function.solvedRequirements)
    (noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []) : RequirementProves context id predicate := by
  have member : required.row ∈ context.solvedRequirements := same.symm ▸ required.member
  exact ⟨required.row, ⟨member, required.identity⟩, required.predicateEq,
    ledger.ordinary_valid member (by simp [noTemplates])⟩

def observeRequired (function : CheckedFunction) (id : RequirementId) (predicate : ProgramPredicate) :
    IO (Required function id predicate) := do
  match found : function.solvedRequirements.find? (fun (row : SolvedRequirement) => decide (row.id = id)) with
  | none => throw (IO.userError "required ledger row missing")
  | some row =>
    let ⟨predicateEq⟩ ← observed (row.predicate = predicate) "required predicate"
    return ⟨row, List.mem_of_find?_eq_some found, of_decide_eq_true (List.find?_some (p := fun (item : SolvedRequirement) => decide (item.id = id)) found), predicateEq⟩

structure RelayShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  localBinder : TypedBinder
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : DirectCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id trait
  initialized : StatementNode
  conditionRead : Read function.typedBody flag .bool
  savedRead : Read function.typedBody localBinder firstType
  loopSecondRead : Read function.typedBody second secondType
  loopCall : DirectCall function.typedBody generic firstParameter secondParameter firstType secondType savedRead.node.id loopSecondRead.node.id trait
  assignment : StatementNode
  resolution : AssignmentResolution
  stop : TypedNode function.typedBody .bool
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
  finalRead : Read function.typedBody localBinder firstType
  finalSecondRead : Read function.typedBody second secondType
  finalCall : DirectCall function.typedBody generic firstParameter secondParameter firstType secondType finalRead.node.id finalSecondRead.node.id trait
  statement : StatementNode
  callRequired : Required function call.requirement (mark trait firstType)
  loopRequired : Required function loopCall.requirement (mark trait firstType)
  finalRequired : Required function finalCall.requirement (mark trait firstType)
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  flagScheme : flag.scheme = .mono .bool
  localScheme : localBinder.scheme = .mono firstType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  flagRequirements : flag.schemeRequirements = []
  localRequirements : localBinder.schemeRequirements = []
  firstClosed : firstType.freeVariables = []
  flagOwner : flag.id.owner = function.typedBody.owner
  localOwner : localBinder.id.owner = function.typedBody.owner
  localOrdinary : localBinder.comptime = false
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  localFirst : localBinder.id ≠ first.id
  localSecond : localBinder.id ≠ second.id
  localFlag : localBinder.id ≠ flag.id
  roots : function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some call.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = localBinder.id
  targetType : resolution.target.type = firstType
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
  statementType : statement.type = firstType

def RelayShape.body {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RelayShape function signature generic firstParameter secondParameter firstType secondType trait) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def RelayShape.nodeList {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RelayShape function signature generic firstParameter secondParameter firstType secondType trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
    .expression shape.call.value.node, .statement shape.initialized,
    .expression shape.conditionRead.node, .expression shape.savedRead.node, .expression shape.loopSecondRead.node,
    .expression shape.loopCall.callee.node, .expression shape.loopCall.value.node, .statement shape.assignment,
    .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
    .expression shape.finalRead.node, .expression shape.finalSecondRead.node, .expression shape.finalCall.callee.node,
    .expression shape.finalCall.value.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType trait}
    (shape : RelayShape function signature generic firstParameter secondParameter firstType secondType trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    (inputTypes : signature.parameterTypes = [firstType, secondType, .bool])
    (returns : signature.returnTypes = [firstType]) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.loop.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [returns]
  let ordinary : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
  let facts : StatementFacts := ⟨firstType, true, true, .returned⟩
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, inputTypes] at extension
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
        have firstFormed := TypeAdmissible.ofWellFormed (types firstType (by simp [inputTypes]))
        have secondFormed := TypeAdmissible.ofWellFormed (types secondType (by simp [inputTypes]))
        have currentLedger := ledger.transportContext
          (flagExtended.context_fields.1.trans (secondExtended.context_fields.1.trans firstExtended.context_fields.1))
          (flagExtended.context_fields.2.2.2.1.trans (secondExtended.context_fields.2.2.2.1.trans firstExtended.context_fields.2.2.2.1))
          (flagExtended.context_fields.2.2.2.2.trans (secondExtended.context_fields.2.2.2.2.trans firstExtended.context_fields.2.2.2.2))
        have rows : lexical.solvedRequirements = function.solvedRequirements := by
          rw [flagExtended.context_fields.2.2.2.2, secondExtended.context_fields.2.2.2.2, firstExtended.context_fields.2.2.2.2]
          rfl
        have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_self))
          (by cases flagExtended; cases secondExtended; exact .tail shape.flagFirst (.tail shape.different firstExtended.local_scheme_requirements_self))
        have secondLookup : lexical.LocalLookup shape.second.id shape.second.scheme := by
          cases flagExtended; exact .tail shape.flagSecond secondExtended.local_self
        have secondRequirements : lexical.LocalSchemeRequirementsLookup shape.second.id shape.second.schemeRequirements := by
          cases flagExtended; exact .tail shape.flagSecond secondExtended.local_scheme_requirements_self
        have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed secondLookup secondRequirements
        have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped
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
        have innerFirst : TypeAdmissible inner firstType := StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := inner) rfl rfl rfl rfl rfl firstFormed
        have innerSecond : TypeAdmissible inner secondType := StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := inner) rfl rfl rfl rfl rfl secondFormed
        have innerBool : TypeAdmissible inner .bool := ⟨innerFirst.1, .builtin .bool⟩
        have innerLedger : ScopedRequirementLedgerWellFormed inner function.typedBody := ScopedRequirementLedgerWellFormed.transportContext (source := lexical) (target := inner) rfl rfl rfl currentLedger
        have conditionTyped := shape.conditionRead.typed flagScheme shape.flagRequirements innerBool
          (.tail shape.localFlag flagExtended.local_self) (.tail shape.localFlag flagExtended.local_scheme_requirements_self)
        have savedTyped := shape.savedRead.typed shape.localScheme shape.localRequirements innerFirst
          localExtended.local_self localExtended.local_scheme_requirements_self
        have loopSecondTyped := shape.loopSecondRead.typed secondScheme shape.secondRequirements innerSecond
          (.tail shape.localSecond secondLookup) (.tail shape.localSecond secondRequirements)
        have loopCallTyped := shape.loopCall.typed (fields ▸ member) innerFirst innerSecond savedTyped loopSecondTyped
          (shape.loopRequired.proves innerLedger rows shape.noTemplates)
        have finalTyped := shape.finalRead.typed shape.localScheme shape.localRequirements innerFirst
          localExtended.local_self localExtended.local_scheme_requirements_self
        have finalSecondTyped := shape.finalSecondRead.typed secondScheme shape.secondRequirements innerSecond
          (.tail shape.localSecond secondLookup) (.tail shape.localSecond secondRequirements)
        have finalCallTyped := shape.finalCall.typed (fields ▸ member) innerFirst innerSecond finalTyped finalSecondTyped
          (shape.finalRequired.proves innerLedger rows shape.noTemplates)
        have stopTyped := shape.stop.ordinary innerBool (shape.stopForm ▸ .reference (.builtinBoolean false))
        have writable : WritableLocal inner shape.resolution.target.root firstType := by
          rw [shape.targetRoot]
          exact .intro localExtended.local_self (shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible innerFirst)
            (by rw [shape.localScheme]; rfl) (by rw [shape.localScheme]; rfl)
        have assigned : StatementHasType function.typedBody ⟨firstType, 1⟩ inner shape.assignment.id inner ordinary :=
          .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
            (.equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
              loopCallTyped shape.assignmentRequirements) shape.assignmentType
        have flagWritable : WritableLocal inner shape.flagResolution.target.root .bool := by
          rw [shape.flagTargetRoot]
          exact .intro (.tail shape.localFlag flagExtended.local_self) (flagScheme.symm ▸ SchemeWellFormed.monoAdmissible innerBool)
            (by rw [flagScheme]; rfl) (by rw [flagScheme]; rfl)
        have flagAssigned : StatementHasType function.typedBody ⟨firstType, 1⟩ inner shape.flagAssignment.id inner ordinary :=
          .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm
            (.equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType)
              stopTyped shape.flagAssignmentRequirements) shape.flagAssignmentType
        have loopTyped := StatementHasType.whileLoop (control := ⟨firstType, 0⟩)
          (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
          (.cons assigned (.singleton flagAssigned)) shape.loopType
        have initializedTyped : StatementHasType function.typedBody ⟨firstType, 0⟩ lexical shape.initialized.id inner ordinary := by
          apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
          · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using callTyped
          · rw [shape.localScheme]; rfl
          · simp [shape.localScheme, SchemeGeneralizes, SchemeGeneralizesExcept, TypeSystem.Scheme.mono, shape.firstClosed]
          · exact localExtended
          · exact shape.initializedType
        exact ⟨inner, .cons initializedTyped (.cons loopTyped (.singleton (.returnValue
          (lookupStatement?_sound shape.statementFound) shape.statementForm finalCallTyped shape.statementType)))⟩


def observeRelay (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RelayShape function signature generic firstParameter secondParameter firstType secondType trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression firstNode, .expression secondNode, .expression initialCallee, .expression initialValue,
      .statement initialized, .expression conditionNode, .expression savedNode, .expression loopSecondNode,
      .expression loopCallee, .expression loopValue, .statement assignment,
      .expression stopNode, .statement flagAssignment, .statement loop,
      .expression finalNode, .expression finalSecondNode, .expression finalCallee, .expression finalValue,
      .statement statement] := function.typedBody.nodes | throw (IO.userError "relay graph")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "relay initialized binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "relay saved assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "relay flag assignment")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first firstNode firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second secondNode secondType
  let call ← observeDirect function.typedBody generic firstParameter secondParameter firstType secondType
    firstRead.node.id secondRead.node.id initialCallee initialValue trait
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let savedRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder savedNode firstType
  let loopSecondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second loopSecondNode secondType
  let loopCall ← observeDirect function.typedBody generic firstParameter secondParameter firstType secondType
    savedRead.node.id loopSecondRead.node.id loopCallee loopValue trait
  let stop ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody stopNode .bool
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder finalNode firstType
  let finalSecondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second finalSecondNode secondType
  let finalCall ← observeDirect function.typedBody generic firstParameter secondParameter firstType secondType
    finalRead.node.id finalSecondRead.node.id finalCallee finalValue trait
  let callRequired ← observeRequired function call.requirement (mark trait firstType)
  let loopRequired ← observeRequired function loopCall.requirement (mark trait firstType)
  let finalRequired ← observeRequired function finalCall.requirement (mark trait firstType)
  let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "relay noTemplates"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "relay inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "relay firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "relay secondScheme"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "relay flagScheme"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono firstType) "relay localScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "relay firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "relay secondRequirements"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "relay flagRequirements"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "relay localRequirements"
  let ⟨firstClosed⟩ ← observed (firstType.freeVariables = []) "relay firstClosed"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "relay flagOwner"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "relay localOwner"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "relay localOrdinary"
  let ⟨different⟩ ← observed (second.id ≠ first.id) "relay different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "relay flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "relay flagSecond"
  let ⟨localFirst⟩ ← observed (localBinder.id ≠ first.id) "relay localFirst"
  let ⟨localSecond⟩ ← observed (localBinder.id ≠ second.id) "relay localSecond"
  let ⟨localFlag⟩ ← observed (localBinder.id ≠ flag.id) "relay localFlag"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]) "relay roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "relay initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some call.value.node.id)) "relay initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "relay initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "relay assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "relay assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "relay assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = localBinder.id) "relay targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = firstType) "relay targetType"
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
  let ⟨statementType⟩ ← observed (statement.type = firstType) "relay statementType"
  return {first, second, flag, localBinder, firstRead, secondRead, call, initialized, conditionRead, savedRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalSecondRead, finalCall, statement, callRequired, loopRequired, finalRequired, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function choose<A, B>(a: A, b: B) returns (A) where A: Mark { return a; }",
    "function relay<A, B>(a: A, b: B, flag: Bool) returns (A) where A: Mark { let saved: A = choose(a, b); while (flag) { saved = choose(saved, b); flag = false; } return choose(saved, b); }",
    "function wordRoot(value: Word, other: Bool, flag: Bool) returns (Word) { return relay(value, other, flag); }",
    "function boolRoot(value: Bool, other: Word, flag: Bool) returns (Bool) { return relay(value, other, flag); }"]}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitId
  chooseFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
  wordFunction : CheckedFunction
  wordSignature : ProgramFunctionSignature
  boolFunction : CheckedFunction
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [chooseFunction, relayFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [chooseSignature, relaySignature, wordSignature, boolSignature]
  methods : program.methods = []
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  chooseRelay : chooseSignature.id ≠ relaySignature.id
  chooseWord : chooseSignature.id ≠ wordSignature.id
  chooseBool : chooseSignature.id ≠ boolSignature.id
  relayWord : relaySignature.id ≠ wordSignature.id
  relayBool : relaySignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  chooseShape : ChooseShape chooseFunction chooseSignature trait
  relayFirstParameter : TypeSystem.TypeParameterId
  relaySecondParameter : TypeSystem.TypeParameterId
  relayScheme : relaySignature.scheme = ⟨[relayFirstParameter, relaySecondParameter], [mark trait (.parameter relayFirstParameter)], .function (.product (.parameter relayFirstParameter) (.product (.parameter relaySecondParameter) .bool)) (.parameter relayFirstParameter)⟩
  relayShape : RelayShape relayFunction relaySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter relayFirstParameter) (.parameter relaySecondParameter) trait
  wordShape : RootShape wordFunction wordSignature relaySignature relayFirstParameter relaySecondParameter .word .bool trait
  boolShape : RootShape boolFunction boolSignature relaySignature relayFirstParameter relaySecondParameter .bool .word trait
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  relayInputTypes : relaySignature.parameterTypes = [(.parameter relayFirstParameter), (.parameter relaySecondParameter), .bool]
  relayReturns : relaySignature.returnTypes = [(.parameter relayFirstParameter)]
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
  wordInputTypes : wordSignature.parameterTypes = [.word, .bool, .bool]
  wordReturns : wordSignature.returnTypes = [.word]
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolInputTypes : boolSignature.parameterTypes = [.bool, .word, .bool]
  boolReturns : boolSignature.returnTypes = [.bool]
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
    | [chooseFunction, relayFunction, wordFunction, boolFunction], [chooseSignature, relaySignature, wordSignature, boolSignature] =>
      let [predicate] := chooseSignature.scheme.predicates | throw (IO.userError "choose predicate")
      let trait := predicate.trait
      let chooseShape ← observeChoose chooseFunction chooseSignature trait
      let [relayFirstParameter, relaySecondParameter] := relaySignature.scheme.parameters | throw (IO.userError "relay parameters")
      let ⟨relayScheme⟩ ← observed (relaySignature.scheme = ⟨[relayFirstParameter, relaySecondParameter], [mark trait (.parameter relayFirstParameter)], .function (.product (.parameter relayFirstParameter) (.product (.parameter relaySecondParameter) .bool)) (.parameter relayFirstParameter)⟩) "relay scheme"
      let relayShape ← observeRelay relayFunction relaySignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter (.parameter relayFirstParameter) (.parameter relaySecondParameter) trait
      let wordShape ← observeRoot wordFunction wordSignature relaySignature relayFirstParameter relaySecondParameter .word .bool trait
      let boolShape ← observeRoot boolFunction boolSignature relaySignature relayFirstParameter relaySecondParameter .bool .word trait
      let ⟨methods⟩ ← observed (program.methods = []) "fixture methods"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "choose declaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
      let ⟨chooseRelay⟩ ← observed (chooseSignature.id ≠ relaySignature.id) "chooseRelay distinct"
      let ⟨chooseWord⟩ ← observed (chooseSignature.id ≠ wordSignature.id) "chooseWord distinct"
      let ⟨chooseBool⟩ ← observed (chooseSignature.id ≠ boolSignature.id) "chooseBool distinct"
      let ⟨relayWord⟩ ← observed (relaySignature.id ≠ wordSignature.id) "relayWord distinct"
      let ⟨relayBool⟩ ← observed (relaySignature.id ≠ boolSignature.id) "relayBool distinct"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "wordBool distinct"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "choose nodes"
      let ⟨relayInputTypes⟩ ← observed (relaySignature.parameterTypes = [(.parameter relayFirstParameter), (.parameter relaySecondParameter), .bool]) "relay original input types"
      let ⟨relayReturns⟩ ← observed (relaySignature.returnTypes = [(.parameter relayFirstParameter)]) "relay original returns"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
      let ⟨wordInputTypes⟩ ← observed (wordSignature.parameterTypes = [.word, .bool, .bool]) "word original input types"
      let ⟨wordReturns⟩ ← observed (wordSignature.returnTypes = [.word]) "word original returns"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "word nodes"
      let ⟨boolInputTypes⟩ ← observed (boolSignature.parameterTypes = [.bool, .word, .bool]) "bool original input types"
      let ⟨boolReturns⟩ ← observed (boolSignature.returnTypes = [.bool]) "bool original returns"
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
          · exact False.elim (chooseRelay (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures]) header ledger relayInputTypes relayReturns
          · exact False.elim (relayWord (relayDeclaration.symm.trans identity))
          · exact False.elim (relayBool (relayDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (identity.symm.trans wordDeclaration))
          · exact False.elim (relayWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) header ledger wordInputTypes wordReturns
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (identity.symm.trans boolDeclaration))
          · exact False.elim (relayBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) header ledger boolInputTypes boolReturns
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep, program, checked, trait, chooseFunction, relayFunction, wordFunction, boolFunction, chooseSignature, relaySignature, wordSignature, boolSignature, functions, signatures, methods, chooseDeclaration, relayDeclaration, wordDeclaration, boolDeclaration, chooseRelay, chooseWord, chooseBool, relayWord, relayBool, wordBool, chooseShape, relayFirstParameter, relaySecondParameter, relayScheme, relayShape, wordShape, boolShape, chooseNodes, relayInputTypes, relayReturns, relayNodes, wordInputTypes, wordReturns, wordNodes, boolInputTypes, boolReturns, boolNodes}
    | _, _ => throw (IO.userError "evidence direct declarations")
end Tests.SourceCoreEvidenceScoped
