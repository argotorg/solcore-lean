import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
import Solcore.Test.SourceSemantics.CoreLowering.Method.Scoped
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Scoped
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedFinalPlanOrigins
import Solcore.SourceSemantics.CoreLowering.CallableSpecializationEquality
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
import Solcore.Frontend.ProgramCheckingFuelAgreement
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection

/-!
# Method origin fixture tests

The fixture of the method origin evidence, its finite method shapes, relay observations and compiler
support.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceResults
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
export Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults (ScalarOutput)
end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode
abbrev CallNode := Tests.SourceCoreEvidenceDirect.CallNode
abbrev observeCallNode := Tests.SourceCoreEvidenceDirect.observeCallNode
abbrev MethodDirect := Tests.SourceCoreEvidenceMethod.DirectCall
abbrev observeMethodDirect := Tests.SourceCoreEvidenceMethod.observeDirect
abbrev TraitShape := Tests.SourceCoreEvidenceMethod.TraitShape
abbrev observeTrait := Tests.SourceCoreEvidenceMethod.observeTrait
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
abbrev RootShape := Tests.SourceCoreMethodScoped.RootShape
abbrev observeRoot := Tests.SourceCoreMethodScoped.observeRoot
abbrev MethodUnary := Tests.SourceCoreMethodScoped.MethodUnary
abbrev observeUnary := Tests.SourceCoreMethodScoped.observeUnary
structure RelayCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId)
    (type : TypeSystem.Ty) (firstArgument secondArgument flagArgument : ExpressionId) (trait : ProgramTraitId) where
  callee : TypedNode source (.function (.product type (.product type .bool)) type)
  value : CallNode source type
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)
  scheme : signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)],
    .function (.product (.parameter parameter) (.product (.parameter parameter) .bool)) (.parameter parameter)⟩
  inputs : signature.parameterTypes = [.parameter parameter, .parameter parameter, .bool]
  returns : signature.returnTypes = [(.parameter parameter)]
  exact : instantiation = ⟨signature.id, [(parameter, type)],
    .function (.product type (.product type .bool)) type, [predicate trait type], signature.parameterComptime, signature.returnComptime⟩

theorem RelayCall.typed {source signature parameter type firstArgument secondArgument flagArgument trait}
    (call : RelayCall source signature parameter type firstArgument secondArgument flagArgument trait)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context type)
    (firstTyped : ExpressionHasType source context firstArgument type)
    (secondTyped : ExpressionHasType source context secondArgument type)
    (flagTyped : ExpressionHasType source context flagArgument .bool)
    (required : RequirementProves context call.requirement (predicate trait type)) :
    ExpressionHasType source context call.value.node.id type := by
  have resultFormed := firstFormed
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
  have application : DeclarationApplicationValid context call.instantiation [type, type, .bool] type [predicate trait type] := by
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
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.cons flagTyped (.nil _)))))
      call.value.raw resultFormed (call.value.type.symm ▸ resultFormed) ?_
    rw [call.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) (.cons required .nil) rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

def observeRelayCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty)
    (firstArgument secondArgument flagArgument : ExpressionId) (callee value : ExpressionNode) (trait : ProgramTraitId) :
    IO (RelayCall source signature parameter type firstArgument secondArgument flagArgument trait) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product type (.product type .bool)) type)
  let value ← observeCallNode source value type
  let [requirement] := value.node.requirements | throw (IO.userError "direct requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "direct requirements"
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument, flagArgument] (.declaration instantiation)) "generic direct form"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[parameter], [predicate trait (.parameter parameter)], .function (.product (.parameter parameter) (.product (.parameter parameter) .bool)) (.parameter parameter)⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter parameter, .parameter parameter, .bool]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [(.parameter parameter)]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(parameter, type)], .function (.product type (.product type .bool)) type, [predicate trait type], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, requirement, requirements, name, instantiation, calleeForm, form, scheme, inputs, returns, exact}


structure RelayShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
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
  inputTypes : signature.parameterTypes = [type, type, .bool]
  returns : signature.returnTypes = [type]
  roots : function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some call.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = localBinder.id
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

def RelayShape.body {function signature type trait}
    (shape : RelayShape function signature type trait) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def RelayShape.nodeList {function signature type trait}
    (shape : RelayShape function signature type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.conditionRead.node, .expression shape.loopSecondRead.node,
   .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.value.node, .statement shape.statement]


theorem RelayShape.statementTyping {function signature type trait}
    (shape : RelayShape function signature type (.declaration trait.id))
    (catalog : TraitShape trait) (signatures : ProgramSignatures) (member : trait ∈ signatures.traits)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.loop.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
  let facts : StatementFacts := ⟨type, true, true, .returned⟩
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts)), rfl, ?_⟩
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
          exact .intro localExtended.local_self (shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible innerFirst)
            (by rw [shape.localScheme]; rfl) (by rw [shape.localScheme]; rfl)
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
        exact ⟨inner, bodyTyped⟩


def observeRelay (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (RelayShape function signature type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression firstNode, .expression initialValue, .statement initialized,
      .expression conditionNode, .expression loopSecondNode, .expression loopValue, .statement assignment,
      .expression stopNode, .statement flagAssignment, .statement loop,
      .expression finalNode, .expression finalValue, .statement statement] := function.typedBody.nodes
      | throw (IO.userError "relay thirteen nodes")
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
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type, type, .bool]) "relay inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [type]) "relay returns"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]) "relay roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "relay initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some call.value.node.id)) "relay initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "relay initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "relay assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "relay assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "relay assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = localBinder.id) "relay targetRoot"
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
  return {inputTypes, returns, first, second, flag, localBinder, firstRead, call, initialized, conditionRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalCall, statement, callRequired, loopRequired, finalRequired, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
structure FactoryShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
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
  call : RelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id trait
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
  expression : TypedNode function.typedBody (closureType type)
  outerReturn : StatementNode
  roots : function.typedBody.roots = [.statement outerReturn.id]
  lambda : expression.node.form = .lambda [] type [statement.id]
  outerReturnFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some expression.node.id)
  outerReturnType : outerReturn.type = closureType type
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = type
  inputTypes : signature.parameterTypes = [type, type, .bool]
  returns : signature.returnTypes = [closureType type]

def FactoryShape.nodeList {function signature generic parameter type trait}
    (shape : FactoryShape function signature generic parameter type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.flagRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement, .expression shape.expression.node, .statement shape.outerReturn]

theorem FactoryShape.statementTyping {function signature generic parameter type trait}
    (shape : FactoryShape function signature generic parameter type trait)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody)
    :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.outerReturn.id] := statementRoots_injective (roots.symm.trans shape.roots)
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
        have callable : TypeAdmissible lexical (closureType type) :=
          ⟨firstFormed.1, .function (.builtin .unit) (TypeAdmissible.typeWellScopedWithin
            (fun _ member => (TypeSystem.Ty.mem_freeVariables_function_iff _ _ _).mpr (.inr member)) firstFormed)⟩
        have lambdaTyped := shape.expression.ordinary callable
          (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
            (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
              shape.statementForm callTyped shape.statementType))
            (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩))
        exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.outerReturnFound)
          shape.outerReturnForm lambdaTyped shape.outerReturnType)⟩
def observeFactory (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (FactoryShape function signature generic parameter type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression readFlag, .expression callee, .expression value, .statement statement, .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst type
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond type
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag readFlag .bool
  let call ← observeRelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id callee value trait
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
    let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType type)
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "factory roots"
    let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] type [statement.id]) "factory lambda"
    let ⟨outerReturnFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "outerReturnFound"
    let ⟨outerReturnForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.node.id)) "outerReturnForm"
    let ⟨outerReturnType⟩ ← observed (outerReturn.type = closureType type) "outerReturnType"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = type) "generic root statementType"
    let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type, type, .bool]) "root inputTypes"
    let ⟨returns⟩ ← observed (signature.returnTypes = [closureType type]) "root returns"
    return {expression, outerReturn, lambda, outerReturnFound, outerReturnForm, outerReturnType, inputTypes, returns, flag, flagRead, flagFirst, flagSecond, flagScheme, flagRequirements, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")


abbrev UseShape := Tests.SourceCoreMethodClosure.UseShape
abbrev observeUse := Tests.SourceCoreMethodClosure.observeUse

/-- The original implementation body retains its own lexical binders and loop. -/
structure MethodShape (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) where
  generic : ProgramFunctionSignature
  genericParameter : TypeSystem.TypeParameterId
  trait : ProgramTraitId
  value : TypedBinder
  saved : TypedBinder
  flag : TypedBinder
  initialRead : Read function.typedBody value type
  initialFlag : TypedNode function.typedBody .bool
  conditionRead : Read function.typedBody flag .bool
  loopRead : Read function.typedBody value type
  stop : TypedNode function.typedBody .bool
  finalRead : Read function.typedBody saved type
  call : MethodDirect function.typedBody generic genericParameter type initialRead.node.id trait
  loopCall : MethodDirect function.typedBody generic genericParameter type loopRead.node.id trait
  finalCall : MethodDirect function.typedBody generic genericParameter type finalRead.node.id trait
  callRequired : Required function call.requirement (predicate trait type)
  loopRequired : Required function loopCall.requirement (predicate trait type)
  finalRequired : Required function finalCall.requirement (predicate trait type)
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  initialized : StatementNode
  flagInitialized : StatementNode
  assignment : StatementNode
  flagAssignment : StatementNode
  loop : StatementNode
  statement : StatementNode
  resolution : AssignmentResolution
  flagResolution : AssignmentResolution
  inputs : function.typedBody.inputs = [value]
  inputTypes : signature.parameterTypes = [type]
  returns : signature.returnTypes = [type]
  valueScheme : value.scheme = .mono type
  savedScheme : saved.scheme = .mono type
  flagScheme : flag.scheme = .mono .bool
  valueRequirements : value.schemeRequirements = []
  savedRequirements : saved.schemeRequirements = []
  flagRequirements : flag.schemeRequirements = []
  valueOwner : value.id.owner = function.typedBody.owner
  savedOwner : saved.id.owner = function.typedBody.owner
  flagOwner : flag.id.owner = function.typedBody.owner
  savedOrdinary : saved.comptime = false
  flagOrdinary : flag.comptime = false
  savedValue : saved.id ≠ value.id
  flagValue : flag.id ≠ value.id
  flagSaved : flag.id ≠ saved.id
  closed : type.freeVariables = []
  roots : function.typedBody.roots = [.statement initialized.id, .statement flagInitialized.id, .statement loop.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl saved (some call.value.node.id)
  initializedType : initialized.type = .unit
  flagInitializedFound : function.typedBody.lookupStatement? flagInitialized.id = some flagInitialized
  flagInitializedForm : flagInitialized.form = .letDecl flag (some initialFlag.node.id)
  flagInitializedType : flagInitialized.type = .unit
  initialFlagForm : initialFlag.node.form = .reference "true" (.builtinBoolean true)
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = saved.id
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

def MethodShape.nodeList {function signature type}
    (shape : MethodShape function signature type) : List Node :=
  [.expression shape.initialRead.node, .expression shape.call.callee.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.initialFlag.node, .statement shape.flagInitialized,
   .expression shape.conditionRead.node, .expression shape.loopRead.node, .expression shape.loopCall.callee.node, .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.callee.node, .expression shape.finalCall.value.node, .statement shape.statement]

theorem MethodShape.statementTyping {function signature type}
    (shape : MethodShape function signature type) (signatures : ProgramSignatures)
    (header : CheckedBodyHeaderWellFormed signatures signature function)
    (member : shape.generic ∈ signatures.functions)
    (ledger : ScopedRequirementLedgerWellFormed (checkedBodyContext signatures signature function) function.typedBody) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.flagInitialized.id, shape.loop.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := ⟨.unit, false, false, .ordinary .unit⟩
  let facts : StatementFacts := ⟨type, true, true, .returned⟩
  refine ⟨BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.cons ordinary (BodyFacts.singleton facts))), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have types := StructuralSubstitution.TypesWellFormed.transportContext
      head.context_fields.1 head.context_fields.2.2.1 head.context_fields.2.1 header.parameter_types
    have formed := TypeAdmissible.ofWellFormed (types type (by simp [shape.inputTypes]))
    have initialTyped := shape.initialRead.typed scheme shape.valueRequirements formed
      head.local_self head.local_scheme_requirements_self
    have fields : lexical.signatures = signatures := head.context_fields.1
    have currentLedger := ledger.transportContext head.context_fields.1
      head.context_fields.2.2.2.1 head.context_fields.2.2.2.2
    have rows : lexical.solvedRequirements = function.solvedRequirements := head.context_fields.2.2.2.2
    have initialCallTyped := shape.call.typed (fields ▸ member) formed initialTyped
      (shape.callRequired.proves currentLedger rows shape.noTemplates)
    let savedContext := lexical.withLocal shape.saved.id shape.saved.scheme shape.saved.schemeRequirements
    have savedExtended : BinderExtends function.typedBody.owner lexical shape.saved savedContext := by
      apply BinderExtends.intro
      · exact { owned := shape.savedOwner
                scheme := shape.savedScheme.symm ▸ SchemeWellFormed.monoAdmissible formed
                quantified_fresh := by rw [shape.savedScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                monomorphic_requirements_empty := fun _ => shape.savedRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext, Context.ofSignatures,
          Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements,
          Context.withResidualTypeVariables, shape.savedValue]
    have savedFormed : TypeAdmissible savedContext type :=
      StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := savedContext) rfl rfl rfl rfl rfl formed
    have savedBool : TypeAdmissible savedContext .bool := ⟨savedFormed.1, .builtin .bool⟩
    have initialFlagTyped := shape.initialFlag.ordinary savedBool (shape.initialFlagForm ▸ .reference (.builtinBoolean true))
    let inner := savedContext.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
    have flagExtended : BinderExtends function.typedBody.owner savedContext shape.flag inner := by
      apply BinderExtends.intro
      · exact { owned := shape.flagOwner
                scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible savedBool
                quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                monomorphic_requirements_empty := fun _ => shape.flagRequirements }
      · cases head
        simp [savedContext, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext, Context.ofSignatures,
          Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements,
          Context.withResidualTypeVariables, shape.flagValue, shape.flagSaved]
    have innerFormed : TypeAdmissible inner type :=
      StructuralSubstitution.TypeAdmissible.transportContext (source := lexical) (target := inner) rfl rfl rfl rfl rfl formed
    have innerBool : TypeAdmissible inner .bool := ⟨innerFormed.1, .builtin .bool⟩
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements innerBool
      flagExtended.local_self flagExtended.local_scheme_requirements_self
    have loopTyped := shape.loopRead.typed scheme shape.valueRequirements innerFormed
      (.tail shape.flagValue (.tail shape.savedValue head.local_self))
      (.tail shape.flagValue (.tail shape.savedValue head.local_scheme_requirements_self))
    have finalTyped := shape.finalRead.typed shape.savedScheme shape.savedRequirements innerFormed
      (.tail shape.flagSaved savedExtended.local_self) (.tail shape.flagSaved savedExtended.local_scheme_requirements_self)
    have innerLedger : ScopedRequirementLedgerWellFormed inner function.typedBody :=
      ScopedRequirementLedgerWellFormed.transportContext (source := lexical) (target := inner) rfl rfl rfl currentLedger
    have loopCallTyped := shape.loopCall.typed (fields ▸ member) innerFormed loopTyped
      (shape.loopRequired.proves innerLedger rows shape.noTemplates)
    have finalCallTyped := shape.finalCall.typed (fields ▸ member) innerFormed finalTyped
      (shape.finalRequired.proves innerLedger rows shape.noTemplates)
    have stopTyped := shape.stop.ordinary innerBool (shape.stopForm ▸ .reference (.builtinBoolean false))
    have writable : WritableLocal inner shape.resolution.target.root type := by
      rw [shape.targetRoot]
      exact .intro (.tail shape.flagSaved savedExtended.local_self) (shape.savedScheme.symm ▸ SchemeWellFormed.monoAdmissible innerFormed)
        (by rw [shape.savedScheme]; rfl) (by rw [shape.savedScheme]; rfl)
    have assigned : StatementHasType function.typedBody ⟨type, 1⟩ inner shape.assignment.id inner ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm
        (.equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
          loopCallTyped shape.assignmentRequirements) shape.assignmentType
    have flagWritable : WritableLocal inner shape.flagResolution.target.root .bool := by
      rw [shape.flagTargetRoot]
      exact .intro flagExtended.local_self (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible innerBool)
        (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
    have flagAssigned : StatementHasType function.typedBody ⟨type, 1⟩ inner shape.flagAssignment.id inner ordinary :=
      .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm
        (.equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType)
          stopTyped shape.flagAssignmentRequirements) shape.flagAssignmentType
    have whileTyped := StatementHasType.whileLoop (control := ⟨type, 0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
      (.cons assigned (.singleton flagAssigned)) shape.loopType
    have initializedTyped : StatementHasType function.typedBody ⟨type, 0⟩ lexical shape.initialized.id savedContext ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.savedScheme, TypeSystem.Scheme.mono] using initialCallTyped
      · rw [shape.savedScheme]; rfl
      · simp [shape.savedScheme, SchemeGeneralizes, SchemeGeneralizesExcept, TypeSystem.Scheme.mono, shape.closed]
      · exact savedExtended
      · exact shape.initializedType
    have flagInitializedTyped : StatementHasType function.typedBody ⟨type, 0⟩ savedContext shape.flagInitialized.id inner ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.flagInitializedFound) shape.flagInitializedForm
      · simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using initialFlagTyped
      · rw [shape.flagScheme]; rfl
      · simp [shape.flagScheme, SchemeGeneralizes, SchemeGeneralizesExcept, TypeSystem.Scheme.mono, show TypeSystem.Ty.bool.freeVariables = [] from rfl]
      · exact flagExtended
      · exact shape.flagInitializedType
    exact ⟨inner, .cons initializedTyped (.cons flagInitializedTyped (.cons whileTyped (.singleton
      (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm finalCallTyped shape.statementType))))⟩

def observeMethod (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) (generic : ProgramFunctionSignature)
    (genericParameter : TypeSystem.TypeParameterId) (trait : ProgramTraitId) : IO {shape : MethodShape function signature type // shape.generic = generic ∧ shape.genericParameter = genericParameter ∧ shape.trait = trait} := do
  let [value] := function.typedBody.inputs | throw (IO.userError "method inputs")
  let [.expression initialNode, .expression initialCallee, .expression initialValue, .statement initialized,
       .expression initialFlagNode, .statement flagInitialized,
       .expression conditionNode, .expression loopNode, .expression loopCallee, .expression loopValue, .statement assignment,
       .expression stopNode, .statement flagAssignment, .statement loop,
       .expression finalNode, .expression finalCallee, .expression finalValue, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "method scoped nodes")
  let .letDecl saved _ := initialized.form | throw (IO.userError "method saved")
  let .letDecl flag _ := flagInitialized.form | throw (IO.userError "method flag")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "method assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "method flag assignment")
  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody value initialNode type
  let initialFlag ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody initialFlagNode .bool
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let loopRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody value loopNode type
  let stop ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody stopNode .bool
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody saved finalNode type
  let call ← observeMethodDirect function.typedBody generic genericParameter type initialRead.node.id initialCallee initialValue trait
  let loopCall ← observeMethodDirect function.typedBody generic genericParameter type loopRead.node.id loopCallee loopValue trait
  let finalCall ← observeMethodDirect function.typedBody generic genericParameter type finalRead.node.id finalCallee finalValue trait
  let callRequired ← observeRequired function call.requirement (predicate trait type)
  let loopRequired ← observeRequired function loopCall.requirement (predicate trait type)
  let finalRequired ← observeRequired function finalCall.requirement (predicate trait type)
  let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "method noTemplates"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [value]) "method inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type]) "method inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [type]) "method returns"
  let ⟨valueScheme⟩ ← observed (value.scheme = .mono type) "method valueScheme"
  let ⟨savedScheme⟩ ← observed (saved.scheme = .mono type) "method savedScheme"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "method flagScheme"
  let ⟨valueRequirements⟩ ← observed (value.schemeRequirements = []) "method valueRequirements"
  let ⟨savedRequirements⟩ ← observed (saved.schemeRequirements = []) "method savedRequirements"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "method flagRequirements"
  let ⟨valueOwner⟩ ← observed (value.id.owner = function.typedBody.owner) "method valueOwner"
  let ⟨savedOwner⟩ ← observed (saved.id.owner = function.typedBody.owner) "method savedOwner"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "method flagOwner"
  let ⟨savedOrdinary⟩ ← observed (saved.comptime = false) "method savedOrdinary"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "method flagOrdinary"
  let ⟨savedValue⟩ ← observed (saved.id ≠ value.id) "method savedValue"
  let ⟨flagValue⟩ ← observed (flag.id ≠ value.id) "method flagValue"
  let ⟨flagSaved⟩ ← observed (flag.id ≠ saved.id) "method flagSaved"
  let ⟨closed⟩ ← observed (type.freeVariables = []) "method closed"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement flagInitialized.id, .statement loop.id, .statement statement.id]) "method roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "method initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl saved (some call.value.node.id)) "method initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "method initializedType"
  let ⟨flagInitializedFound⟩ ← observed (function.typedBody.lookupStatement? flagInitialized.id = some flagInitialized) "method flagInitializedFound"
  let ⟨flagInitializedForm⟩ ← observed (flagInitialized.form = .letDecl flag (some initialFlag.node.id)) "method flagInitializedForm"
  let ⟨flagInitializedType⟩ ← observed (flagInitialized.type = .unit) "method flagInitializedType"
  let ⟨initialFlagForm⟩ ← observed (initialFlag.node.form = .reference "true" (.builtinBoolean true)) "method initialFlagForm"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "method assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "method assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "method assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = saved.id) "method targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = type) "method targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "method targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "method assignmentRequirements"
  let ⟨stopForm⟩ ← observed (stop.node.form = .reference "false" (.builtinBoolean false)) "method stopForm"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "method flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stop.node.id) "method flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "method flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "method flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "method flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "method flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "method flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "method loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "method loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "method loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "method statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalCall.value.node.id)) "method statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "method statementType"
  return ⟨{
    generic := generic
    genericParameter := genericParameter
    trait := trait
    call := call
    loopCall := loopCall
    finalCall := finalCall
    callRequired := callRequired
    loopRequired := loopRequired
    finalRequired := finalRequired
    noTemplates := noTemplates
    value := value
    saved := saved
    flag := flag
    initialRead := initialRead
    initialFlag := initialFlag
    conditionRead := conditionRead
    loopRead := loopRead
    stop := stop
    finalRead := finalRead
    initialized := initialized
    flagInitialized := flagInitialized
    assignment := assignment
    flagAssignment := flagAssignment
    loop := loop
    statement := statement
    resolution := resolution
    flagResolution := flagResolution
    inputs := inputs
    inputTypes := inputTypes
    returns := returns
    valueScheme := valueScheme
    savedScheme := savedScheme
    flagScheme := flagScheme
    valueRequirements := valueRequirements
    savedRequirements := savedRequirements
    flagRequirements := flagRequirements
    valueOwner := valueOwner
    savedOwner := savedOwner
    flagOwner := flagOwner
    savedOrdinary := savedOrdinary
    flagOrdinary := flagOrdinary
    savedValue := savedValue
    flagValue := flagValue
    flagSaved := flagSaved
    closed := closed
    roots := roots
    initializedFound := initializedFound
    initializedForm := initializedForm
    initializedType := initializedType
    flagInitializedFound := flagInitializedFound
    flagInitializedForm := flagInitializedForm
    flagInitializedType := flagInitializedType
    initialFlagForm := initialFlagForm
    assignmentFound := assignmentFound
    assignmentForm := assignmentForm
    assignmentType := assignmentType
    targetRoot := targetRoot
    targetType := targetType
    targetBare := targetBare
    assignmentRequirements := assignmentRequirements
    stopForm := stopForm
    flagAssignmentFound := flagAssignmentFound
    flagAssignmentForm := flagAssignmentForm
    flagAssignmentType := flagAssignmentType
    flagTargetRoot := flagTargetRoot
    flagTargetType := flagTargetType
    flagTargetBare := flagTargetBare
    flagAssignmentRequirements := flagAssignmentRequirements
    loopFound := loopFound
    loopForm := loopForm
    loopType := loopType
    statementFound := statementFound
    statementForm := statementForm
    statementType := statementType
  }, ⟨rfl, rfl, rfl⟩⟩

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
  shape : MethodShape function
    (implementation.functionSignatureOfMethodWithTrait trait method) type
  genericMember : shape.generic ∈ program.signatures.functions

theorem ImplementationShape.statementTyping {program implementation type}
    (given : ImplementationShape program implementation type)
    (catalog : SignatureCatalogWellFormed program.signatures)
    (implementationMember : implementation ∈ program.signatures.implementations)
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
  have implementationFormed := catalog.implementations_semantic implementation implementationMember
  have methodMember : given.method ∈ implementation.methods := by rw [given.methods]; simp
  have methodFormed := implementationFormed.methods given.method methodMember
  obtain ⟨semanticTrait, traitMethod, semanticTraitMember, selectedHeadTrait,
    traitMethodMember, traitMethodId, _, _, _, _, _, _⟩ := methodFormed.trait_method
  have rawLookup : program.signatures.traits.find?
      (fun candidate => decide (candidate.id = given.method.traitMethod.trait)) = some given.trait := by
    simpa [ProgramSignatures.trait?] using given.traitLookup
  have selectedMember : given.trait ∈ program.signatures.traits := List.mem_of_find?_eq_some rawLookup
  have selectedId : given.trait.id = given.method.traitMethod.trait :=
    of_decide_eq_true (List.find?_some
      (p := fun candidate : ProgramTraitSignature => decide (candidate.id = given.method.traitMethod.trait)) rawLookup)
  have traitMethodFormed := (catalog.traits_semantic semanticTrait semanticTraitMember).methods traitMethod traitMethodMember
  have semanticId : semanticTrait.id = given.method.traitMethod.trait := by
    rw [← traitMethodFormed.owner]
    exact congrArg ProgramTraitMethodId.trait traitMethodId
  have traitEq : given.trait = semanticTrait :=
    Frontend.trait_signature_eq_of_mem_of_id_eq catalog.trait_ids
      selectedMember semanticTraitMember (selectedId.trans semanticId.symm)
  have headTrait : implementation.head.trait = .declaration given.trait.id := by
    rw [traitEq]
    exact selectedHeadTrait
  have predicatesFixed := methodAssumptions_applySubstitution_eq_self catalog
    implementationMember methodMember selectedMember headTrait given.function.substitution
  have ledger : ScopedRequirementLedgerWellFormed
      (checkedBodyContext program.signatures (implementation.functionSignatureOfMethodWithTrait given.trait given.method) given.function)
      given.function.typedBody := by
    apply ScopedRequirementLedgerWellFormed.transportContext
      (source := SourceInferenceSoundness.checkedFinalizedRequirementContext program.signatures
        (implementation.functionSignatureOfMethodWithTrait given.trait given.method) given.function)
      (target := checkedBodyContext program.signatures
        (implementation.functionSignatureOfMethodWithTrait given.trait given.method) given.function)
    · rfl
    · simpa only [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        SourceInferenceSoundness.checkedFinalizedRequirementContext,
        ProgramImplementationSignature.functionSignatureOfMethodWithTrait,
        ProgramImplementationSignature.functionSignatureOfMethod] using predicatesFixed.symm
    · rfl
    · exact SourceInferenceSoundness.checkFunctionBody_success_scopedRequirementLedgerWellFormed given.checked
  have header := CheckedBodyHeaderWellFormed.ofCheckImplementationMethod implementationFormed methodFormed given.checked
  exact given.shape.statementTyping program.signatures header given.genericMember ledger

def observeImplementation (program : CheckedProgram) (implementation : ProgramImplementationSignature)
    (type : TypeSystem.Ty) (generic : ProgramFunctionSignature)
    (genericParameter : TypeSystem.TypeParameterId) (mark : ProgramTraitId)
    (genericMember : generic ∈ program.signatures.functions) : IO (ImplementationShape program implementation type) := do
  match methods : implementation.methods with
  | [method] =>
    match traitLookup : program.signatures.trait? method.traitMethod.trait with
    | none => throw (IO.userError "method trait missing")
    | some trait =>
      match checked : checkFunctionBody program.environment program.signatures
          (implementation.functionSignatureOfMethodWithTrait trait method) 1024 with
      | .error error => throw (IO.userError (reprStr error))
      | .ok function =>
        let ⟨shape, sameGeneric⟩ ← observeMethod function
          (implementation.functionSignatureOfMethodWithTrait trait method) type generic genericParameter mark
        have genericMember : shape.generic ∈ program.signatures.functions := sameGeneric.1.symm ▸ genericMember
        return {method, trait, function, methods, traitLookup, checked, shape, genericMember}
  | _ => throw (IO.userError "implementation method count")

def content : String := String.intercalate "\n" [
  "trait Seed<T> {}", "impl<T> Seed<T> {}",
  "trait Mark<T> {}", "impl<T> Mark<T> where T: Seed {}",
  "function identity<T>(value: T) returns (T) where T: Mark { return value; }",
  "trait BitNot<T> { function bnot(value: T) returns (T); }",
  "impl<T> BitNot<T> where T: Mark { function bnot(value: T) returns (T) { let saved = identity(value); let flag = true; while (flag) { saved = identity(value); flag = false; } return identity(saved); } }",
  "function relay<T>(value: T, next: T, flag: Bool) returns (T) where T: BitNot { let current = ~value; while (flag) { current = ~next; flag = false; } return ~current; }",
  "function make<T>(value: T, next: T, flag: Bool) returns (function() returns (T)) where T: BitNot { return lam() -> T { return relay(value, next, flag); }; }",
  "function wordRoot(value: Word, next: Word, flag: Bool) returns (function() returns (Word)) { return make(value, next, flag); }",
  "function boolRoot(value: Bool, next: Bool, flag: Bool) returns (function() returns (Bool)) { return make(value, next, flag); }",
  "function useWord(f: function() returns (Word)) returns (Word) { return f(); }",
  "function useBool(f: function() returns (Bool)) returns (Bool) { return f(); }"]


def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] }

structure IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) (type : TypeSystem.Ty) where
  binder : TypedBinder
  read : Read function.typedBody binder type
  statement : StatementNode
  inputs : function.typedBody.inputs = [binder]
  inputTypes : signature.parameterTypes = [type]
  returns : signature.returnTypes = [type]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = type

def IdentityShape.nodeList {function signature type} (shape : IdentityShape function signature type) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

theorem IdentityShape.statementTyping {function signature type}
    (shape : IdentityShape function signature type) (signatures : ProgramSignatures)
    (header : CheckedBodyHeaderWellFormed signatures signature function) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := ⟨type, true, true, .returned⟩
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head rest =>
    cases rest
    have types := StructuralSubstitution.TypesWellFormed.transportContext
      head.context_fields.1 head.context_fields.2.2.1 head.context_fields.2.1 header.parameter_types
    have formed := TypeAdmissible.ofWellFormed (types type (by simp [shape.inputTypes]))
    have read := shape.read.typed scheme shape.binderRequirements formed head.local_self head.local_scheme_requirements_self
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.statementForm read shape.statementType)⟩

def observeIdentity (function : CheckedFunction) (signature : ProgramFunctionSignature)
    (type : TypeSystem.Ty) : IO (IdentityShape function signature type) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity binder")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "identity nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder node type
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "identity inputs"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [type]) "identity inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [type]) "identity returns"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "identity binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "identity roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "identity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "identity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "identity statementType"
  return {binder, read, statement, inputs, inputTypes, returns, binderRequirements, roots, statementFound, statementForm, statementType}

/-- Original checked declarations and their independent Source statement typing.
Method bodies retain genuine implementation signatures. -/
structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1024 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  trait : ProgramTraitSignature
  traitShape : TraitShape trait
  seed : ProgramTraitSignature
  mark : ProgramTraitSignature
  traits : program.signatures.traits = [seed, mark, trait]
  identityParameter : TypeSystem.TypeParameterId
  identityFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  identityDeclaration : identityFunction.declaration = identitySignature.id
  identityShape : IdentityShape identityFunction identitySignature (.parameter identityParameter)
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  parameter : TypeSystem.TypeParameterId
  relayParameter : TypeSystem.TypeParameterId
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
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
  functions : program.functions = [identityFunction, relayFunction, makeFunction, wordFunction, boolFunction, useWordFunction, useBoolFunction]
  signatures : program.signatures.functions = [identitySignature, relaySignature, makeSignature, wordSignature, boolSignature, useWordSignature, useBoolSignature]
  methodCount : program.methods.length = 1
  implementation : ProgramImplementationSignature
  seedImplementation : ProgramImplementationSignature
  seedMethods : seedImplementation.methods = []
  markImplementation : ProgramImplementationSignature
  markParameter : TypeSystem.TypeParameterId
  markParameters : markImplementation.parameters = [markParameter]
  markPredicates : markImplementation.wherePredicates = [predicate (.declaration seed.id) (.parameter markParameter)]
  markMethods : markImplementation.methods = []
  implementationParameter : TypeSystem.TypeParameterId
  implementationParameters : implementation.parameters = [implementationParameter]
  implementationPredicates : implementation.wherePredicates = [predicate (.declaration mark.id) (.parameter implementationParameter)]
  implementations : program.signatures.implementations = [seedImplementation, markImplementation, implementation]
  methodShape : ImplementationShape program implementation (.parameter implementationParameter)
  relayDeclaration : relayFunction.declaration = relaySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  useWordDeclaration : useWordFunction.declaration = useWordSignature.id
  useBoolDeclaration : useBoolFunction.declaration = useBoolSignature.id
  relayShape : RelayShape relayFunction relaySignature (.parameter relayParameter) (.declaration trait.id)
  makeShape : FactoryShape makeFunction makeSignature relaySignature relayParameter (.parameter parameter) (.declaration trait.id)
  wordShape : RootShape wordFunction wordSignature makeSignature parameter .word (.declaration trait.id)
  boolShape : RootShape boolFunction boolSignature makeSignature parameter .bool (.declaration trait.id)
  useWordShape : UseShape useWordFunction useWordSignature .word
  useBoolShape : UseShape useBoolFunction useBoolSignature .bool
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
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
    | [identityFunction, relayFunction, makeFunction, wordFunction, boolFunction, useWordFunction, useBoolFunction],
        [identitySignature, relaySignature, makeSignature, wordSignature, boolSignature, useWordSignature, useBoolSignature],
        [seed, mark, trait], [seedImplementation, markImplementation, implementation] =>
      let traitShape ← observeTrait trait
      let [identityParameter] := identitySignature.scheme.parameters | throw (IO.userError "identity parameter")
      let identityShape ← observeIdentity identityFunction identitySignature (.parameter identityParameter)
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity nodes"
      let ⟨seedMethods⟩ ← observed (seedImplementation.methods = []) "generic Seed methods"
      let [markParameter] := markImplementation.parameters | throw (IO.userError "generic Mark parameter")
      let ⟨markParameters⟩ ← observed (markImplementation.parameters = [markParameter]) "generic Mark parameters"
      let ⟨markPredicates⟩ ← observed
        (markImplementation.wherePredicates = [predicate (.declaration seed.id) (.parameter markParameter)])
        "genuine nested Mark evidence premise"
      let ⟨markMethods⟩ ← observed (markImplementation.methods = []) "generic Mark methods"
      match implementationParameters : implementation.parameters with
      | [implementationParameter] =>
        let ⟨implementationPredicates⟩ ← observed
          (implementation.wherePredicates = [predicate (.declaration mark.id) (.parameter implementationParameter)])
          "original method implementation own assumption"
        let [parameter] := makeSignature.scheme.parameters | throw (IO.userError "make generic parameter")
        let [relayParameter] := relaySignature.scheme.parameters | throw (IO.userError "relay generic parameter")
        let relayShape ← observeRelay relayFunction relaySignature (.parameter relayParameter) (.declaration trait.id)
        let makeShape ← observeFactory makeFunction makeSignature relaySignature relayParameter (.parameter parameter) (.declaration trait.id)
        let wordShape ← observeRoot wordFunction wordSignature makeSignature parameter .word (.declaration trait.id)
        let boolShape ← observeRoot boolFunction boolSignature makeSignature parameter .bool (.declaration trait.id)
        let useWordShape ← observeUse useWordFunction useWordSignature .word
        let useBoolShape ← observeUse useBoolFunction useBoolSignature .bool
        let methodShape ← observeImplementation program implementation (.parameter implementationParameter)
          identitySignature identityParameter (.declaration mark.id) (by simp [signatures])
        let ⟨methodCount⟩ ← observed (program.methods.length = 1) "original generic method inventory"
        let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
        let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
        let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "word declaration"
        let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "bool declaration"
        let ⟨useWordDeclaration⟩ ← observed (useWordFunction.declaration = useWordSignature.id) "useWord declaration"
        let ⟨useBoolDeclaration⟩ ← observed (useBoolFunction.declaration = useBoolSignature.id) "useBool declaration"
        let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
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
            rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · have same : candidate = identitySignature := eq_of_mem_of_nodup_map
                (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
                (by simp [signatures]) (identity.symm.trans identityDeclaration)
              subst candidate
              exact identityShape.statementTyping program.signatures header
            · have same : candidate = relaySignature := eq_of_mem_of_nodup_map
                (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
                (by simp [signatures]) (identity.symm.trans relayDeclaration)
              subst candidate
              exact relayShape.statementTyping traitShape program.signatures (by simp [traits]) header ledger
            · have same : candidate = makeSignature := eq_of_mem_of_nodup_map
                (SignatureCatalogWellFormed.ofCheckProgram checked).function_ids candidateMember
                (by simp [signatures]) (identity.symm.trans makeDeclaration)
              subst candidate
              exact makeShape.statementTyping program.signatures (by simp [signatures]) header ledger
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
            rcases member with rfl | rfl | rfl
            · simp only [seedMethods, List.not_mem_nil] at methodMember
            · simp only [markMethods, List.not_mem_nil] at methodMember
            · exact methodShape.statementTyping (SignatureCatalogWellFormed.ofCheckProgram checked)
                (by simp [implementations]) methodMember lookup accepted }
        return {wellFormed := programWellFormed_ofCheckProgram_statements checked deep,
                program, checked, trait, traitShape, traits, seed, mark, identityParameter, identityFunction, identitySignature,
                identityDeclaration, identityShape, identityNodes, seedImplementation, seedMethods, markImplementation, markParameter, markParameters, markPredicates, markMethods, implementation, implementationParameter, implementationParameters, implementationPredicates, methodShape, parameter, relayParameter, relayFunction, relaySignature, relayDeclaration, relayShape, relayNodes,
                makeFunction, makeSignature, wordFunction, wordSignature, boolFunction, boolSignature, useWordFunction, useWordSignature, useBoolFunction, useBoolSignature,
                functions, signatures, methodCount, implementations,
                makeDeclaration, wordDeclaration, boolDeclaration, useWordDeclaration, useBoolDeclaration,
                makeShape, wordShape, boolShape, useWordShape, useBoolShape,
                makeNodes, wordNodes, boolNodes, useWordNodes, useBoolNodes}
      | _ => throw (IO.userError "generic implementation parameter")
    | _, _, _, _ => throw (IO.userError "method closure original declaration inventory")

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
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
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id,
    SourceCompiler.Seed.declaration checked.useWordSignature.id, SourceCompiler.Seed.declaration checked.useBoolSignature.id]
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
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  named : SourceCoreGeneralFunctions.Function
  cached : fixture.recipe.compiled.indexed.base.functions[index]? = some named
  same : named.specialized = row
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
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      let ⟨named, cached, same⟩ ← (do
        match cached : fixture.recipe.compiled.indexed.base.functions[index]? with
        | none => throw (IO.userError "actual cached declaration missing")
        | some named =>
          let ⟨same⟩ ← observed ((named.specialized == row) = true) "actual cached declaration record"
          return ⟨named, cached, eq_of_beq same⟩ :
        IO {named : SourceCoreGeneralFunctions.Function //
          fixture.recipe.compiled.indexed.base.functions[index]? = some named ∧ named.specialized = row})
      return {
        origin := origin
        named := named
        cached := cached
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
  obtain ⟨prepared⟩ := RecursiveNamedPreparedFinalPlanOrigins.of_cached_origin fixture.recipe.compiled observed.cached observed.same observed.origin
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
  started : session.start observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions (.ok (.succeeded completion))
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
    match started : session.start observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions
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

structure SelectedRelayShape (function : CheckedFunction) (type : TypeSystem.Ty) where
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
  roots : function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some call.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = localBinder.id
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

def SelectedRelayShape.body {function type}
    (shape : SelectedRelayShape function type) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def SelectedRelayShape.nodeList {function type}
    (shape : SelectedRelayShape function type) : List Node :=
  [.expression shape.firstRead.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.conditionRead.node, .expression shape.loopSecondRead.node,
   .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.value.node, .statement shape.statement]


def observeSelectedRelay (function : CheckedFunction) (type : TypeSystem.Ty) :
    IO (SelectedRelayShape function type) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression firstNode, .expression initialValue, .statement initialized,
      .expression conditionNode, .expression loopSecondNode, .expression loopValue, .statement assignment,
      .expression stopNode, .statement flagAssignment, .statement loop,
      .expression finalNode, .expression finalValue, .statement statement] := function.typedBody.nodes
      | throw (IO.userError "relay thirteen nodes")
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
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]) "relay roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "relay initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some call.value.node.id)) "relay initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "relay initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "relay assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "relay assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "relay assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = localBinder.id) "relay targetRoot"
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
  return {first, second, flag, localBinder, firstRead, call, initialized, conditionRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalCall, statement, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
structure SelectedFactoryShape (function : CheckedFunction) (generic : ProgramFunctionSignature)
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
  call : RelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id trait
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
  expression : TypedNode function.typedBody (closureType type)
  outerReturn : StatementNode
  roots : function.typedBody.roots = [.statement outerReturn.id]
  lambda : expression.node.form = .lambda [] type [statement.id]
  outerReturnFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some expression.node.id)
  outerReturnType : outerReturn.type = closureType type
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = type

def SelectedFactoryShape.nodeList {function generic parameter type trait}
    (shape : SelectedFactoryShape function generic parameter type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.flagRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement, .expression shape.expression.node, .statement shape.outerReturn]

def observeSelectedFactory (function : CheckedFunction) (generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (SelectedFactoryShape function generic parameter type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression readFlag, .expression callee, .expression value, .statement statement, .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst type
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond type
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag readFlag .bool
  let call ← observeRelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id callee value trait
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
    let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType type)
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "factory roots"
    let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] type [statement.id]) "factory lambda"
    let ⟨outerReturnFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "outerReturnFound"
    let ⟨outerReturnForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.node.id)) "outerReturnForm"
    let ⟨outerReturnType⟩ ← observed (outerReturn.type = closureType type) "outerReturnType"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = type) "generic root statementType"
    return {expression, outerReturn, lambda, outerReturnFound, outerReturnForm, outerReturnType, flag, flagRead, flagFirst, flagSecond, flagScheme, flagRequirements, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")


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

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  makeWordRow : ObservedRow fixture fixture.makeSignature
  makeBoolRow : ObservedRow fixture fixture.makeSignature
  relayWordRow : ObservedRow fixture fixture.relaySignature
  relayBoolRow : ObservedRow fixture fixture.relaySignature
  useWordRow : ObservedRoot fixture fixture.useWordSignature
  useBoolRow : ObservedRoot fixture fixture.useBoolSignature
  identityWordRow : ObservedRow fixture fixture.identitySignature
  identityBoolRow : ObservedRow fixture fixture.identitySignature
  identityWordShape : SelectedIdentityShape identityWordRow.row.function .word
  identityBoolShape : SelectedIdentityShape identityBoolRow.row.function .bool
  identityWordNodes : identityWordRow.row.function.typedBody.nodes = identityWordShape.nodeList
  identityBoolNodes : identityBoolRow.row.function.typedBody.nodes = identityBoolShape.nodeList
  identityWordResultType : identityWordRow.row.function.inferredBodyType = .word
  identityBoolResultType : identityBoolRow.row.function.inferredBodyType = .bool
  identityWordKey : identityWordRow.row.key = ⟨fixture.identitySignature.id, [.word]⟩
  identityBoolKey : identityBoolRow.row.key = ⟨fixture.identitySignature.id, [.bool]⟩
  identityWordInstantiation : CallableNamedCanonicalOrder.retainedInstantiation identityWordRow.row =
    ⟨fixture.identitySignature.id, [(fixture.identityParameter, .word)], .function .word .word,
      [predicate (.declaration fixture.mark.id) .word], fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩
  identityBoolInstantiation : CallableNamedCanonicalOrder.retainedInstantiation identityBoolRow.row =
    ⟨fixture.identitySignature.id, [(fixture.identityParameter, .bool)], .function .bool .bool,
      [predicate (.declaration fixture.mark.id) .bool], fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  makeWordShape : SelectedFactoryShape makeWordRow.row.function fixture.relaySignature fixture.relayParameter .word (.declaration fixture.trait.id)
  makeBoolShape : SelectedFactoryShape makeBoolRow.row.function fixture.relaySignature fixture.relayParameter .bool (.declaration fixture.trait.id)
  relayWordShape : SelectedRelayShape relayWordRow.row.function .word
  relayBoolShape : SelectedRelayShape relayBoolRow.row.function .bool
  useWordShape : UseShape useWordRow.row.function fixture.useWordSignature .word
  useBoolShape : UseShape useBoolRow.row.function fixture.useBoolSignature .bool
  wordInputScheme : wordShape.first.scheme = .mono (.word)
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = closureType .word
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolInputScheme : boolShape.first.scheme = .mono (.bool)
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  boolResultType : boolRow.row.function.inferredBodyType = closureType .bool
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  makeWordInputScheme : makeWordShape.first.scheme = .mono (.word)
  makeWordNodes : makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList
  makeWordResultType : makeWordRow.row.function.inferredBodyType = closureType .word
  makeWordKey : makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩
  makeBoolInputScheme : makeBoolShape.first.scheme = .mono (.bool)
  makeBoolNodes : makeBoolRow.row.function.typedBody.nodes = makeBoolShape.nodeList
  makeBoolResultType : makeBoolRow.row.function.inferredBodyType = closureType .bool
  makeBoolKey : makeBoolRow.row.key = ⟨fixture.makeSignature.id, [.bool]⟩
  useWordInputScheme : useWordShape.body.binder.scheme = .mono (closureType .word)
  useWordNodes : useWordRow.row.function.typedBody.nodes = useWordShape.nodeList
  useWordResultType : useWordRow.row.function.inferredBodyType = .word
  useWordKey : useWordRow.row.key = ⟨fixture.useWordSignature.id, []⟩
  useBoolInputScheme : useBoolShape.body.binder.scheme = .mono (closureType .bool)
  useBoolNodes : useBoolRow.row.function.typedBody.nodes = useBoolShape.nodeList
  useBoolResultType : useBoolRow.row.function.inferredBodyType = .bool
  useBoolKey : useBoolRow.row.key = ⟨fixture.useBoolSignature.id, []⟩
  relayWordNodes : relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList
  relayWordResultType : relayWordRow.row.function.inferredBodyType = .word
  relayWordKey : relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word]⟩
  makeWordRelayInstantiation : makeWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row
  relayBoolNodes : relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList
  relayBoolResultType : relayBoolRow.row.function.inferredBodyType = .bool
  relayBoolKey : relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool]⟩
  makeBoolRelayInstantiation : makeBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row
  ordinarySlotsDistinct : [wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, relayWordRow.index, relayBoolRow.index, useWordRow.index, useBoolRow.index, identityWordRow.index, identityBoolRow.index].Nodup
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 12
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let makeWordRow ← observeRow fixture fixture.makeSignature [.word]
  let makeBoolRow ← observeRow fixture fixture.makeSignature [.bool]
  let relayWordRow ← observeRow fixture fixture.relaySignature [.word]
  let relayBoolRow ← observeRow fixture fixture.relaySignature [.bool]
  let useWordRow ← observeRootRow fixture fixture.useWordSignature
  let useBoolRow ← observeRootRow fixture fixture.useBoolSignature
  let identityWordRow ← observeRow fixture fixture.identitySignature [.word]
  let identityBoolRow ← observeRow fixture fixture.identitySignature [.bool]
  let identityWordShape ← observeSelectedIdentity identityWordRow.row.function .word
  let identityBoolShape ← observeSelectedIdentity identityBoolRow.row.function .bool
  let ⟨identityWordNodes⟩ ← observed (identityWordRow.row.function.typedBody.nodes = identityWordShape.nodeList) "identityWord nodes"
  let ⟨identityBoolNodes⟩ ← observed (identityBoolRow.row.function.typedBody.nodes = identityBoolShape.nodeList) "identityBool nodes"
  let ⟨identityWordResultType⟩ ← observed (identityWordRow.row.function.inferredBodyType = .word) "identityWord type"
  let ⟨identityBoolResultType⟩ ← observed (identityBoolRow.row.function.inferredBodyType = .bool) "identityBool type"
  let ⟨identityWordKey⟩ ← observed (identityWordRow.row.key = ⟨fixture.identitySignature.id, [.word]⟩) "identityWord key"
  let ⟨identityBoolKey⟩ ← observed (identityBoolRow.row.key = ⟨fixture.identitySignature.id, [.bool]⟩) "identityBool key"
  let ⟨identityWordInstantiation⟩ ← observed (CallableNamedCanonicalOrder.retainedInstantiation identityWordRow.row =
    ⟨fixture.identitySignature.id, [(fixture.identityParameter, .word)], .function .word .word,
      [predicate (.declaration fixture.mark.id) .word], fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩) "identityWord actual instantiation"
  let ⟨identityBoolInstantiation⟩ ← observed (CallableNamedCanonicalOrder.retainedInstantiation identityBoolRow.row =
    ⟨fixture.identitySignature.id, [(fixture.identityParameter, .bool)], .function .bool .bool,
      [predicate (.declaration fixture.mark.id) .bool], fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩) "identityBool actual instantiation"
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  let makeWordShape ← observeSelectedFactory makeWordRow.row.function fixture.relaySignature fixture.relayParameter .word (.declaration fixture.trait.id)
  let makeBoolShape ← observeSelectedFactory makeBoolRow.row.function fixture.relaySignature fixture.relayParameter .bool (.declaration fixture.trait.id)
  let relayWordShape ← observeSelectedRelay relayWordRow.row.function .word
  let relayBoolShape ← observeSelectedRelay relayBoolRow.row.function .bool
  let useWordShape ← observeUse useWordRow.row.function fixture.useWordSignature .word
  let useBoolShape ← observeUse useBoolRow.row.function fixture.useBoolSignature .bool
  let ⟨wordInputScheme⟩ ← observed (wordShape.first.scheme = .mono (.word)) "actual method closure wordInputScheme"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "actual method closure wordNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = closureType .word) "actual method closure wordResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "actual method closure wordKey"
  let ⟨boolInputScheme⟩ ← observed (boolShape.first.scheme = .mono (.bool)) "actual method closure boolInputScheme"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "actual method closure boolNodes"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = closureType .bool) "actual method closure boolResultType"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "actual method closure boolKey"
  let ⟨makeWordInputScheme⟩ ← observed (makeWordShape.first.scheme = .mono (.word)) "actual method closure makeWordInputScheme"
  let ⟨makeWordNodes⟩ ← observed (makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList) "actual method closure makeWordNodes"
  let ⟨makeWordResultType⟩ ← observed (makeWordRow.row.function.inferredBodyType = closureType .word) "actual method closure makeWordResultType"
  let ⟨makeWordKey⟩ ← observed (makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩) "actual method closure makeWordKey"
  let ⟨makeBoolInputScheme⟩ ← observed (makeBoolShape.first.scheme = .mono (.bool)) "actual method closure makeBoolInputScheme"
  let ⟨makeBoolNodes⟩ ← observed (makeBoolRow.row.function.typedBody.nodes = makeBoolShape.nodeList) "actual method closure makeBoolNodes"
  let ⟨makeBoolResultType⟩ ← observed (makeBoolRow.row.function.inferredBodyType = closureType .bool) "actual method closure makeBoolResultType"
  let ⟨makeBoolKey⟩ ← observed (makeBoolRow.row.key = ⟨fixture.makeSignature.id, [.bool]⟩) "actual method closure makeBoolKey"
  let ⟨useWordInputScheme⟩ ← observed (useWordShape.body.binder.scheme = .mono (closureType .word)) "actual method closure useWordInputScheme"
  let ⟨useWordNodes⟩ ← observed (useWordRow.row.function.typedBody.nodes = useWordShape.nodeList) "actual method closure useWordNodes"
  let ⟨useWordResultType⟩ ← observed (useWordRow.row.function.inferredBodyType = .word) "actual method closure useWordResultType"
  let ⟨useWordKey⟩ ← observed (useWordRow.row.key = ⟨fixture.useWordSignature.id, []⟩) "actual method closure useWordKey"
  let ⟨useBoolInputScheme⟩ ← observed (useBoolShape.body.binder.scheme = .mono (closureType .bool)) "actual method closure useBoolInputScheme"
  let ⟨useBoolNodes⟩ ← observed (useBoolRow.row.function.typedBody.nodes = useBoolShape.nodeList) "actual method closure useBoolNodes"
  let ⟨useBoolResultType⟩ ← observed (useBoolRow.row.function.inferredBodyType = .bool) "actual method closure useBoolResultType"
  let ⟨useBoolKey⟩ ← observed (useBoolRow.row.key = ⟨fixture.useBoolSignature.id, []⟩) "actual method closure useBoolKey"
  let ⟨relayWordNodes⟩ ← observed (relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList) "relayWord nodes"
  let ⟨relayWordResultType⟩ ← observed (relayWordRow.row.function.inferredBodyType = .word) "relayWord result"
  let ⟨relayWordKey⟩ ← observed (relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word]⟩) "relayWord key"
  let ⟨makeWordRelayInstantiation⟩ ← observed (makeWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row) "makeWordRelayInstantiation"
  let ⟨relayBoolNodes⟩ ← observed (relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList) "relayBool nodes"
  let ⟨relayBoolResultType⟩ ← observed (relayBoolRow.row.function.inferredBodyType = .bool) "relayBool result"
  let ⟨relayBoolKey⟩ ← observed (relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool]⟩) "relayBool key"
  let ⟨makeBoolRelayInstantiation⟩ ← observed (makeBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row) "makeBoolRelayInstantiation"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row) "actual method closure wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row) "actual method closure boolInstantiation"
  let ⟨ordinarySlotsDistinct⟩ ← observed ([wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, relayWordRow.index, relayBoolRow.index, useWordRow.index, useBoolRow.index, identityWordRow.index, identityBoolRow.index].Nodup) "actual method closure ordinarySlotsDistinct"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 12) "actual method closure globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]) "actual method closure entryKeys"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual method closure noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual method closure profile"
  return {identityWordRow, identityBoolRow, identityWordShape, identityBoolShape, identityWordNodes, identityBoolNodes, identityWordResultType, identityBoolResultType, identityWordKey, identityBoolKey, identityWordInstantiation, identityBoolInstantiation, relayWordRow, relayBoolRow, relayWordShape, relayBoolShape, relayWordNodes, relayWordResultType, relayWordKey, makeWordRelayInstantiation, relayBoolNodes, relayBoolResultType, relayBoolKey, makeBoolRelayInstantiation, wordRow, boolRow, makeWordRow, makeBoolRow, useWordRow, useBoolRow, wordShape, boolShape, makeWordShape, makeBoolShape, useWordShape, useBoolShape, wordInputScheme, wordNodes, wordResultType, wordKey, boolInputScheme, boolNodes, boolResultType, boolKey, makeWordInputScheme, makeWordNodes, makeWordResultType, makeWordKey, makeBoolInputScheme, makeBoolNodes, makeBoolResultType, makeBoolKey, useWordInputScheme, useWordNodes, useWordResultType, useWordKey, useBoolInputScheme, useBoolNodes, useBoolResultType, useBoolKey, wordInstantiation, boolInstantiation, ordinarySlotsDistinct, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCatalog
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure GenericImplementation (implementation : ProgramImplementationSignature) : Prop where
  head : ∃ parameter, implementation.parameters = [parameter] ∧ implementation.head.subject = .parameter parameter
  arguments : implementation.head.arguments = []
  methods : ∀ method, method ∈ implementation.methods → method.wherePredicates = []

theorem GenericImplementation.formed {implementation : ProgramImplementationSignature}
    (given : GenericImplementation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  obtain ⟨parameter, parameters, subject⟩ := given.head
  refine ⟨parameters ▸ List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_, ?_, ?_⟩
  · intro metavariable
    simp [TypedTraitResolution.VariableOccursInPredicate, subject, given.arguments, TypeSystem.Ty.freeVariables]
  · intro actual occurs
    have same : parameter = actual := by
      simpa [TypedTraitResolution.ParameterOccursInPredicate, subject, given.arguments,
        TypeSystem.TypeParameterOccurs] using occurs
    rw [parameters, ← same]
    simp
  · intro predicate predicateMember actual _occurs
    rw [given.methods method member] at predicateMember
    cases predicateMember

def observeGenericImplementation (implementation : ProgramImplementationSignature) :
    IO (PLift (GenericImplementation implementation)) := do
  match parameters : implementation.parameters with
  | [parameter] =>
    let ⟨subject⟩ ← observed (implementation.head.subject = .parameter parameter) "generic implementation head"
    let ⟨arguments⟩ ← observed (implementation.head.arguments = []) "method implementation head arguments"
    let ⟨methods⟩ ← observed (implementation.methods.all (fun method => decide (method.wherePredicates = [])) = true) "method predicates"
    return ⟨⟨⟨parameter, parameters, subject⟩, arguments, fun method member =>
      of_decide_eq_true (List.all_eq_true.mp methods method member)⟩⟩
  | _ => throw (IO.userError "generic implementation parameter")

private def observeGenericImplementations : (implementations : List ProgramImplementationSignature) →
    IO (PLift (∀ implementation, implementation ∈ implementations → GenericImplementation implementation))
  | [] => pure ⟨by intro implementation member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← observeGenericImplementation first
    let ⟨tail⟩ ← observeGenericImplementations rest
    return ⟨by
      intro implementation member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail implementation member⟩

/-- The actual final compiler table issues the method evidence prerequisites.
Implementation assumptions are retained, while complete dictionary agreement
is checked internally by the executable resolver receipt. -/
def observeMethodCatalog (fixture : CompiledFixture) :
    IO (PLift (CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)) := do
  let compiled := fixture.recipe.compiled
  let ⟨shapes⟩ ← observeGenericImplementations compiled.sourceProgram.signatures.implementations
  let some ⟨ready⟩ := CallableMethodOriginTable.validate compiled.sourceProgram compiled.indexed.base.plan.specializations
    | throw (IO.userError "actual method materializer/resolver and origin table is unsupported")
  return ⟨⟨⟨fun implementation member _method methodMember =>
    (shapes implementation member).formed methodMember⟩, ready⟩⟩

theorem CompiledFixture.loaded (fixture : CompiledFixture) :
    ∃ loaded, Frontend.checkLoadedProgram loaded 1024 = .ok fixture.recipe.compiled.sourceProgram := by
  obtain ⟨loaded, _loaded, checked⟩ := checkProgram_success_load fixture.checked
  exact ⟨loaded, fixture.sameProgram.symm ▸ checked⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFactorySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

structure ObservedFactory (fixture : CompiledFixture) {function : CheckedFunction} {generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape function generic parameter type trait) where
  owned : shape.expression.node.id.occurrence.owner = function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    function.typedBody shape.expression.node.id = .ok (shape.expression.node, reported)

private def confirm (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFactorySupport (fixture : CompiledFixture) {function : CheckedFunction} {generic : ProgramFunctionSignature}
    {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
    (shape : SelectedFactoryShape function generic parameter type trait) : IO (ObservedFactory fixture shape) := do
  let ⟨owned⟩ ← confirm (shape.expression.node.id.occurrence.owner = function.typedBody.owner) "factory lambda owner"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      function.typedBody shape.expression.node.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = shape.expression.node) "factory lambda node"
    return ⟨owned, reported, by simpa only [same] using read⟩

structure ObservedFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  word : ObservedFactory fixture observed.makeWordShape
  bool : ObservedFactory fixture observed.makeBoolShape

def observeFactories (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedFactories fixture observed) := do
  return ⟨← observeFactorySupport fixture observed.makeWordShape,
    ← observeFactorySupport fixture observed.makeBoolShape⟩

theorem ActualHeader.factory_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {generic : ProgramFunctionSignature} {parameter : TypeSystem.TypeParameterId}
    {type : TypeSystem.Ty} {trait : ProgramTraitId} (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (extra : ObservedFactory fixture shape) (actual : ActualHeader fixture row.row)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {stages : Staging.Recursive.Registry} :
    ∃ terminal : Terminal actual.header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ :=
    actual.terminal shape.expression.node.id shape.outerReturn shape.roots shape.outerReturnFound shape.outerReturnForm
  refine ⟨terminal, ?_⟩
  apply CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_actual terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile
    observed.wordRow.entryMember (node := shape.expression.node) (reported := extra.reported)
  · rw [actual.source, expression]; exact shape.expression.found
  · exact shape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact shape.expression.requirements
  · exact shape.expression.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact shape.statementFound
  · exact shape.statementForm
  · exact shape.statementType
  · exact point

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFuelFixture
/-! The companion check retains the same complete original program at fuel
1000. Its original successful receipt is kept for public support issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics

structure OriginalCheckAt1000 (fixture : CompiledFixture) : Prop where
  accepted : checkProgram workspace 1000 = .ok fixture.program
  nonemptyMethods : fixture.program.methods.length = 1

def observeOriginalCheckAt1000 (fixture : CompiledFixture) : IO (PLift (OriginalCheckAt1000 fixture)) := do
  match accepted : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    have same := checkProgram_success_unique_fuel accepted fixture.checked
    pure ⟨⟨by simpa only [same] using accepted, fixture.methodCount⟩⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
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
  makeWordInput : Input fixture.recipe.compiled
  makeWordSame : makeWordInput.row = observed.makeWordRow.row
  makeWordPacket : Issued makeWordInput
  makeWordHeader : ActualHeader fixture observed.makeWordRow.row
  makeWordAligned : makeWordHeader.header = makeWordPacket.header
  makeWordSlot : makeWordHeader.header.slot = observed.makeWordRow.index
  makeWordSignature : makeWordHeader.header.named.signature = observed.makeWordRow.global
  makeBoolInput : Input fixture.recipe.compiled
  makeBoolSame : makeBoolInput.row = observed.makeBoolRow.row
  makeBoolPacket : Issued makeBoolInput
  makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row
  makeBoolAligned : makeBoolHeader.header = makeBoolPacket.header
  makeBoolSlot : makeBoolHeader.header.slot = observed.makeBoolRow.index
  makeBoolSignature : makeBoolHeader.header.named.signature = observed.makeBoolRow.global
  relayWordInput : Input fixture.recipe.compiled
  relayWordSame : relayWordInput.row = observed.relayWordRow.row
  relayWordPacket : Issued relayWordInput
  relayWordHeader : ActualHeader fixture observed.relayWordRow.row
  relayWordAligned : relayWordHeader.header = relayWordPacket.header
  relayWordSlot : relayWordHeader.header.slot = observed.relayWordRow.index
  relayWordSignature : relayWordHeader.header.named.signature = observed.relayWordRow.global
  relayBoolInput : Input fixture.recipe.compiled
  relayBoolSame : relayBoolInput.row = observed.relayBoolRow.row
  relayBoolPacket : Issued relayBoolInput
  relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row
  relayBoolAligned : relayBoolHeader.header = relayBoolPacket.header
  relayBoolSlot : relayBoolHeader.header.slot = observed.relayBoolRow.index
  relayBoolSignature : relayBoolHeader.header.named.signature = observed.relayBoolRow.global
  useWordInput : Input fixture.recipe.compiled
  useWordSame : useWordInput.row = observed.useWordRow.row
  useWordPacket : Issued useWordInput
  useWordHeader : ActualHeader fixture observed.useWordRow.row
  useWordAligned : useWordHeader.header = useWordPacket.header
  useWordSlot : useWordHeader.header.slot = observed.useWordRow.index
  useWordSignature : useWordHeader.header.named.signature = observed.useWordRow.global
  useBoolInput : Input fixture.recipe.compiled
  useBoolSame : useBoolInput.row = observed.useBoolRow.row
  useBoolPacket : Issued useBoolInput
  useBoolHeader : ActualHeader fixture observed.useBoolRow.row
  useBoolAligned : useBoolHeader.header = useBoolPacket.header
  useBoolSlot : useBoolHeader.header.slot = observed.useBoolRow.index
  useBoolSignature : useBoolHeader.header.named.signature = observed.useBoolRow.global
  identityWordInput : Input fixture.recipe.compiled
  identityWordSame : identityWordInput.row = observed.identityWordRow.row
  identityWordPacket : Issued identityWordInput
  identityWordHeader : ActualHeader fixture observed.identityWordRow.row
  identityWordAligned : identityWordHeader.header = identityWordPacket.header
  identityWordSlot : identityWordHeader.header.slot = observed.identityWordRow.index
  identityWordSignature : identityWordHeader.header.named.signature = observed.identityWordRow.global
  identityBoolInput : Input fixture.recipe.compiled
  identityBoolSame : identityBoolInput.row = observed.identityBoolRow.row
  identityBoolPacket : Issued identityBoolInput
  identityBoolHeader : ActualHeader fixture observed.identityBoolRow.row
  identityBoolAligned : identityBoolHeader.header = identityBoolPacket.header
  identityBoolSlot : identityBoolHeader.header.slot = observed.identityBoolRow.index
  identityBoolSignature : identityBoolHeader.header.named.signature = observed.identityBoolRow.global

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.relayWordInput, given.relayBoolInput, given.useWordInput, given.useBoolInput, given.identityWordInput, given.identityBoolInput] :=
  .cons given.wordPacket (.cons given.boolPacket (.cons given.makeWordPacket (.cons given.makeBoolPacket (.cons given.relayWordPacket (.cons given.relayBoolPacket (.cons given.useWordPacket (.cons given.useBoolPacket (.cons given.identityWordPacket (.cons given.identityBoolPacket (.nil))))))))))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature⟩ := observed.makeWordRow.issue
  obtain ⟨makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature⟩ := observed.makeBoolRow.issue
  obtain ⟨relayWordInput, relayWordSame, relayWordPacket, relayWordHeader, relayWordAligned, relayWordSlot, relayWordSignature⟩ := observed.relayWordRow.issue
  obtain ⟨relayBoolInput, relayBoolSame, relayBoolPacket, relayBoolHeader, relayBoolAligned, relayBoolSlot, relayBoolSignature⟩ := observed.relayBoolRow.issue
  obtain ⟨useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature⟩ := observed.useWordRow.issue
  obtain ⟨useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature⟩ := observed.useBoolRow.issue
  obtain ⟨identityWordInput, identityWordSame, identityWordPacket, identityWordHeader, identityWordAligned, identityWordSlot, identityWordSignature⟩ := observed.identityWordRow.issue
  obtain ⟨identityBoolInput, identityBoolSame, identityBoolPacket, identityBoolHeader, identityBoolAligned, identityBoolSlot, identityBoolSignature⟩ := observed.identityBoolRow.issue
  exact ⟨{wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature, boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature, makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature, makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature, relayWordInput, relayWordSame, relayWordPacket, relayWordHeader, relayWordAligned, relayWordSlot, relayWordSignature, relayBoolInput, relayBoolSame, relayBoolPacket, relayBoolHeader, relayBoolAligned, relayBoolSlot, relayBoolSignature, useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature, useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature, identityWordInput, identityWordSame, identityWordPacket, identityWordHeader, identityWordAligned, identityWordSlot, identityWordSignature, identityBoolInput, identityBoolSame, identityBoolPacket, identityBoolHeader, identityBoolAligned, identityBoolSlot, identityBoolSignature}⟩

theorem OrdinaryInventory.word_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.wordHeader.header ∈ headers given.rows := by
  rw [given.wordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.bool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.boolHeader.header ∈ headers given.rows := by
  rw [given.boolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.makeWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeWordHeader.header ∈ headers given.rows := by
  rw [given.makeWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.makeBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.makeBoolHeader.header ∈ headers given.rows := by
  rw [given.makeBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.relayWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.relayWordHeader.header ∈ headers given.rows := by
  rw [given.relayWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.relayBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.relayBoolHeader.header ∈ headers given.rows := by
  rw [given.relayBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.useWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useWordHeader.header ∈ headers given.rows := by
  rw [given.useWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.useBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useBoolHeader.header ∈ headers given.rows := by
  rw [given.useBoolAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.identityWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.identityWordHeader.header ∈ headers given.rows := by
  rw [given.identityWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.identityBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.identityBoolHeader.header ∈ headers given.rows := by
  rw [given.identityBoolAligned]
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

/-- The four actual public entries are covered by their ordinary Source
headers; the complete physical cache separately retains both method slots. -/
theorem OrdinaryInventory.public_coverage {fixture observed}
    (given : OrdinaryInventory fixture observed) :
    RecursiveNamedPublicRootCoverage.Coverage
      (compiled := fixture.recipe.compiled)
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (headers given.rows) := by
  intro entry member named slot found
  have entryKey : entry.key ∈ [observed.wordRow.row.key, observed.boolRow.row.key,
      observed.useWordRow.row.key, observed.useBoolRow.row.key] := by
    rw [← observed.entryKeys]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have namedKey : named.signature.key = entry.key := of_decide_eq_true (List.find?_some (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = entry.key)) found)
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled
    (List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryKey
  rcases entryKey with same | same | same | same
  · have slots := observed.wordRow.global_slot selected (namedKey.trans same)
    exact ⟨given.wordHeader.header, given.word_member, given.wordSlot.trans slots.2.symm⟩
  · have slots := observed.boolRow.global_slot selected (namedKey.trans same)
    exact ⟨given.boolHeader.header, given.bool_member, given.boolSlot.trans slots.2.symm⟩
  · have slots := observed.useWordRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useWordHeader.header, given.useWord_member, given.useWordSlot.trans slots.2.symm⟩
  · have slots := observed.useBoolRow.global_slot selected (namedKey.trans same)
    exact ⟨given.useBoolHeader.header, given.useBool_member, given.useBoolSlot.trans slots.2.symm⟩

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceFactoryCompilerSupport
/-! Actual factory Headers retain the original returned lambda and its body.
The same two factory roots complete the shared program certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {row : ObservedRow fixture signature} {generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}

theorem ActualHeader.factory_compiler_roots
    (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (actual : ActualHeader fixture row.row) :
    actual.header.function.body = [shape.outerReturn.id] := by
  rw [actual.aligned.function]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, shape.roots] at accepted
  exact (Except.ok.inj accepted).symm


/-- The exact accepted returned-lambda action supplies the formation receipt.
Original source facts identify the outer and inner returns without scanning. -/
theorem ActualHeader.factory_compiler_certificate
    (shape : SelectedFactoryShape row.row.function generic parameter type trait)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled row.named) := by
  have issued := AcceptedNamedFactoryAdmission.of_returning actual.prepared actual.aligned
    (actual.factory_compiler_roots shape)
    (by rw [actual.source]; exact shape.outerReturnFound) shape.outerReturnForm
    (by rw [actual.source]; exact shape.expression.found) shape.lambda
    shape.expression.requirements shape.expression.coercions
    (by simp only [noLocals, List.find?_nil])
    (by rw [actual.source]; exact shape.statementFound) shape.statementForm fixture.source_wellFormed
  obtain ⟨certificate⟩ := issued
  exact AcceptedNamedFactoryAdmission.source_of_header actual.prepared actual.aligned
    row.cached row.same certificate

theorem ObservedProgram.makeWord_factory_certificate (observed : ObservedProgram fixture) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled observed.makeWordRow.named) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeWordHeader.factory_compiler_certificate observed.makeWordShape observed.noLocals

theorem ObservedProgram.makeBool_factory_certificate (observed : ObservedProgram fixture) :
    Nonempty (CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate fixture.recipe.compiled observed.makeBoolRow.named) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed
  exact inventory.makeBoolHeader.factory_compiler_certificate observed.makeBoolShape observed.noLocals

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
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
    exact retained_ordered observed.makeWordRow.target observed.makeWordRow.record

theorem ObservedProgram.bool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.makeBoolRow.target observed.makeBoolRow.record

theorem ObservedProgram.makeWord_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.makeWordShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.makeWordShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.makeWordRelayInstantiation]
    exact retained_ordered observed.relayWordRow.target observed.relayWordRow.record

theorem ObservedProgram.makeBool_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Supported fixture.recipe.compiled.indexed.base.plan observed.makeBoolShape.call.instantiation := by
  refine ⟨?_, ?_⟩
  · intro parameter replacement member
    rw [observed.makeBoolShape.call.exact] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [observed.makeBoolRelayInstantiation]
    exact retained_ordered observed.relayBoolRow.target observed.relayBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : RootShape function signature generic parameter type trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨ node = shape.flagRead.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [Tests.SourceCoreMethodScoped.RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.flagRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.flagRead.coercions
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
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · exact .leaf (.read shape.secondRead.found shape.secondRead.form)
  · exact .leaf (.read shape.flagRead.found shape.flagRead.form)
end Root

section Factory
variable {function : CheckedFunction} {generic : ProgramFunctionSignature}
  {parameter : TypeSystem.TypeParameterId} {type : TypeSystem.Ty} {trait : ProgramTraitId}
  (shape : SelectedFactoryShape function generic parameter type trait)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedFactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨ node = shape.flagRead.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node ∨ node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedFactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem SelectedFactoryShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.flagRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.lambda] at form; cases form

include nodes in
theorem SelectedFactoryShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inl shape.secondRead.requirements
    · exact .inl shape.flagRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
    · exact .inl shape.expression.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.flagRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem SelectedFactoryShape.inner_syntax :
    GeneralSyntax function.typedBody shape.call.value.node.id (fun inst => inst = shape.call.instantiation) := by
  refine .direct shape.call.value.found shape.call.form rfl ?_
  intro id member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · exact .leaf (.read shape.secondRead.found shape.secondRead.form)
  · exact .leaf (.read shape.flagRead.found shape.flagRead.form)
end Factory

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
end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMethodSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (NoIndirectSource)
private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {resultType : TypeSystem.Ty} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (expression : ExpressionNode)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = resultType)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression.id))
    (annotation : node.type = resultType) (leaf : approved expression.id)
    (typed : StatementHasType source {returnType := resultType} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) resultType := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation expressionFound expressionType
        (by simpa only [expressionType] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder : TypedBinder} {payload resultType : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (expression : ExpressionNode)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal expression.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved expression.id)
    (typed : SourceAssignmentHasType source context assignment .equal expression.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) resultType) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) resultType := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, expression, expressionFound, by simpa only [← target, targetType, expressionType] using rhs⟩
          · exact remaining


private theorem initialized_syntax {source : TypedSource} {context middle : SourceSemantics.Context}
    {binder : TypedBinder} {payload resultType : TypeSystem.Ty} {node : StatementNode} {expression : ExpressionNode}
    {approved : ExpressionId → Prop} {rest : List StatementId}
    (found : source.lookupStatement? node.id = some node)
    (form : node.form = .letDecl binder (some expression.id))
    (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
    (scheme : binder.scheme = .mono payload)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = payload) (leaf : approved expression.id)
    (typed : Dynamic.StatementHasType.FormTyping source {returnType := resultType} context node.form middle)
    (remaining : GenericImperativeMatch.Syntax source approved middle (.statements true rest) resultType) :
    GenericImperativeMatch.Syntax source approved context (.statements true (node.id :: rest)) resultType := by
  rw [form] at typed
  cases typed with
  | letInitialized value mono extended =>
    exact .initialized found form declaration mono extended ordinary expressionFound
      (by rw [expressionType, scheme]; rfl)
      (by simpa only [scheme, TypeSystem.Scheme.mono, expressionType] using value) leaf remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [scheme]; rfl))


section Metadata
variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : MethodShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)
include nodes in
theorem MethodShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.initialRead.node ∨ node = shape.call.callee.node ∨ node = shape.call.value.node ∨ node = shape.initialFlag.node ∨ node = shape.conditionRead.node ∨ node = shape.loopRead.node ∨ node = shape.loopCall.callee.node ∨ node = shape.loopCall.value.node ∨ node = shape.stop.node ∨ node = shape.finalRead.node ∨ node = shape.finalCall.callee.node ∨ node = shape.finalCall.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [MethodShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem MethodShape.direct_source : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource function.typedBody := by
  intro id node found
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · exact .inl ⟨_, _, shape.initialRead.form⟩
  · exact .inl ⟨_, _, shape.call.calleeForm⟩
  · exact .inr ⟨_, _, _, shape.call.form⟩
  · exact .inl ⟨_, _, shape.initialFlagForm⟩
  · exact .inl ⟨_, _, shape.conditionRead.form⟩
  · exact .inl ⟨_, _, shape.loopRead.form⟩
  · exact .inl ⟨_, _, shape.loopCall.calleeForm⟩
  · exact .inr ⟨_, _, _, shape.loopCall.form⟩
  · exact .inl ⟨_, _, shape.stopForm⟩
  · exact .inl ⟨_, _, shape.finalRead.form⟩
  · exact .inl ⟨_, _, shape.finalCall.calleeForm⟩
  · exact .inr ⟨_, _, _, shape.finalCall.form⟩

include nodes in
theorem MethodShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.direct_source nodes id node found with ⟨name, binder, same⟩ | ⟨name, value, instantiation, same⟩ <;>
    rw [same] at form <;> cases form

include nodes in
theorem MethodShape.metadata {compiled : SourceCoreUnifiedCompilation.Compiled}
    {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : compiled.indexed.base.locals.bindings = []) :
    MetadataFor compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.initialRead.requirements
    · exact .inl shape.call.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.call.form⟩))
    · exact .inl shape.initialFlag.requirements
    · exact .inl shape.conditionRead.requirements
    · exact .inl shape.loopRead.requirements
    · exact .inl shape.loopCall.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.loopCall.form⟩))
    · exact .inl shape.stop.requirements
    · exact .inl shape.finalRead.requirements
    · exact .inl shape.finalCall.callee.requirements
    · exact .inr (.inr (.inl ⟨_, _, _, shape.finalCall.form⟩))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact shape.initialRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
    · exact shape.initialFlag.coercions
    · exact shape.conditionRead.coercions
    · exact shape.loopRead.coercions
    · exact shape.loopCall.callee.coercions
    · exact shape.loopCall.value.coercions
    · exact shape.stop.coercions
    · exact shape.finalRead.coercions
    · exact shape.finalCall.callee.coercions
    · exact shape.finalCall.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]
end Metadata

section Body
variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : MethodShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem MethodShape.saved_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.saved.id = .ok shape.saved := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, MethodShape.nodeList,
    shape.call.calleeForm, shape.call.form, shape.loopCall.calleeForm, shape.loopCall.form, shape.finalCall.calleeForm, shape.finalCall.form,
    shape.initialRead.form, shape.initialFlagForm, shape.conditionRead.form, shape.loopRead.form, shape.stopForm, shape.finalRead.form,
    shape.initializedForm, shape.flagInitializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm,
    shape.savedOwner, shape.savedScheme, TypeSystem.Scheme.mono, shape.savedRequirements, Ne.symm shape.savedValue, shape.flagSaved]

include nodes in
theorem MethodShape.flag_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.flag.id = .ok shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, MethodShape.nodeList,
    shape.call.calleeForm, shape.call.form, shape.loopCall.calleeForm, shape.loopCall.form, shape.finalCall.calleeForm, shape.finalCall.form,
    shape.initialRead.form, shape.initialFlagForm, shape.conditionRead.form, shape.loopRead.form, shape.stopForm, shape.finalRead.form,
    shape.initializedForm, shape.flagInitializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm,
    shape.flagOwner, shape.flagScheme, TypeSystem.Scheme.mono, shape.flagRequirements, Ne.symm shape.flagValue, Ne.symm shape.flagSaved]

def MethodShape.body : List StatementId :=
  [shape.initialized.id, shape.flagInitialized.id, shape.loop.id, shape.statement.id]

theorem MethodShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true shape.body :=
  .initialized shape.initializedFound shape.initializedForm
    (.initialized shape.flagInitializedFound shape.flagInitializedForm
      (.whileLoop shape.loopFound shape.loopForm
        (.assign shape.assignmentFound shape.assignmentForm (.inl rfl) shape.targetBare
          (.assign shape.flagAssignmentFound shape.flagAssignmentForm (.inl rfl) shape.flagTargetBare .nil))
        (.returnValue [] shape.statementFound shape.statementForm)))

def MethodShape.childIds : List ExpressionId :=
  [shape.call.value.node.id, shape.initialFlag.node.id, shape.conditionRead.node.id,
    shape.loopCall.value.node.id, shape.stop.node.id, shape.finalCall.value.node.id]

include nodes in
theorem MethodShape.body_syntax
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ shape.childIds, approved id)
    (typed : StatementsHaveType function.typedBody {returnType := type}
      context shape.body final facts) :
    GenericImperativeMatch.Syntax function.typedBody approved context
      (.statements true shape.body) type := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax shape.initializedFound shape.initializedForm
    (shape.saved_declaration nodes) shape.savedScheme
    (by simp [shape.inputs, Ne.symm shape.savedValue])
    shape.call.value.found shape.call.value.type (leaves _ (by simp [childIds]))
    (form_at unique shape.initializedFound initialized)
  obtain ⟨inner, _, _, flagInitialized, body⟩ := head_tail tail
  apply initialized_syntax shape.flagInitializedFound shape.flagInitializedForm
    (shape.flag_declaration nodes) shape.flagScheme
    (by simp [shape.inputs, Ne.symm shape.flagValue])
    shape.initialFlag.found shape.initialFlag.type (leaves _ (by simp [childIds]))
    (form_at unique shape.flagInitializedFound flagInitialized)
  obtain ⟨middle, _, _, first, suffix⟩ := head_tail body
  have firstForm := form_at unique shape.loopFound first
  rw [shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop shape.loopFound shape.loopForm
      shape.conditionRead.found shape.conditionRead.type
      (by simpa only [shape.conditionRead.type] using conditionTyped) (leaves _ (by simp [childIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique shape.assignmentFound assignedHead
      rw [shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned shape.loopCall.value.node shape.loopCall.value.found shape.loopCall.value.type
          shape.assignmentFound shape.assignmentForm
          (by rw [shape.targetRoot]; exact shape.saved_declaration nodes)
          shape.savedScheme shape.targetBare shape.targetType
          (leaves _ (by simp [childIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique shape.flagAssignmentFound flagHead
        rw [shape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned shape.stop.node shape.stop.found shape.stop.type
            shape.flagAssignmentFound shape.flagAssignmentForm
            (by rw [shape.flagTargetRoot]; exact shape.flag_declaration nodes)
            shape.flagScheme shape.flagTargetBare shape.flagTargetType
            (leaves _ (by simp [childIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail suffix
      exact returning unique shape.finalCall.value.node shape.finalCall.value.found shape.finalCall.value.type
        shape.statementFound shape.statementForm shape.statementType (leaves _ (by simp [childIds])) returningHead
end Body

def MethodShape.DirectSites {function signature type}
    (shape : MethodShape function signature type) (instantiation : DeclarationInstantiation) : Prop :=
  instantiation = shape.call.instantiation ∨ instantiation = shape.loopCall.instantiation ∨ instantiation = shape.finalCall.instantiation

theorem MethodShape.children {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (shape : MethodShape function signature type) :
    ∀ id ∈ shape.childIds, GeneralSyntax function.typedBody id shape.DirectSites := by
  intro id member
  simp only [MethodShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · apply CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntaxFor.direct shape.call.value.found shape.call.form (.inl rfl)
    intro id member
    cases List.mem_singleton.mp member
    exact .leaf (.read shape.initialRead.found shape.initialRead.form)
  · exact .leaf (.literal shape.initialFlag.found (shape.initialFlagForm ▸ .bool _ _))
  · exact .leaf (.read shape.conditionRead.found shape.conditionRead.form)
  · apply CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntaxFor.direct shape.loopCall.value.found shape.loopCall.form (.inr (.inl rfl))
    intro id member
    cases List.mem_singleton.mp member
    exact .leaf (.read shape.loopRead.found shape.loopRead.form)
  · exact .leaf (.literal shape.stop.found (shape.stopForm ▸ .bool _ _))
  · apply CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntaxFor.direct shape.finalCall.value.found shape.finalCall.form (.inr (.inr rfl))
    intro id member
    cases List.mem_singleton.mp member
    exact .leaf (.read shape.finalRead.found shape.finalRead.form)

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMethodCompilerSupport
/-! Original finite method shapes identify the accepted compiler tree and its
children. Source typing and expression grammar are supplied by the genuine
method compilation producer, with the complete selected substitution retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow AcceptedNamedBodyFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)

variable {function : CheckedFunction} {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
  (shape : MethodShape function signature type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes

theorem MethodShape.local_assignable :
    Assignable function.typedBody shape.resolution .equal := by
  refine ⟨.inl rfl, shape.targetBare, ?_⟩
  intro binder found
  rw [shape.targetRoot, shape.saved_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.savedScheme, shape.targetType]
  rfl

theorem MethodShape.flag_assignable :
    Assignable function.typedBody shape.flagResolution .equal := by
  refine ⟨.inl rfl, shape.flagTargetBare, ?_⟩
  intro binder found
  rw [shape.flagTargetRoot, shape.flag_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.flagScheme, shape.flagTargetType]
  rfl

omit nodes in
private theorem assignment_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statement : StatementNode} {assignment : AssignmentResolution} {expression : ExpressionId}
    {rest : List StatementId} {childIds : List ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (statement.id :: rest) code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .assignValue assignment .equal expression)
    (assignable : Assignable source assignment .equal)
    (tail : ∀ {fuel scope code},
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest code) →
      remaining.Ready → remaining.closed = true ∧ remaining.bindings = [] ∧
        remaining.children.map (·.expression) = childIds) :
    tree.closed = true ∧ tree.bindings = [] ∧
      tree.children.map (·.expression) = expression :: childIds := by
  cases tree with
  | assigning read original _ remaining assigned =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (ready.1 (.inl assignable))
  | projectedAssigned read original _ remaining receipt route =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (receipt.projected assignable.2.1)
  | assigned read original _ remaining receipt targetType =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      obtain ⟨closed, bindings, children⟩ := tail remaining ready
      exact ⟨closed, bindings, by simpa only [Tree.children, List.map_cons] using congrArg (List.cons expression) children⟩
  | initialized read original | absent read original | returning read original
  | returnUnit read original | whileLoop read original
  | discard read original | block read original | conditional read original
  | tailValue read original | valueDiscard read original
  | matching read original | matched read original
  | bitNotting read original | bitNotted read original | projectedBitNotted read original
  | forLoop read original | forBoundary read original | breaking read original | continuing read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


omit nodes in
private theorem returning_children {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statement : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope [statement.id] code)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    tree.children.map (·.expression) = [expression] := by
  cases tree with
  | returning read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      rfl
  | initialized read original | absent read original | returnUnit read original
  | whileLoop read original | assigning read original | assigned read original | projectedAssigned read original
  | discard read original | block read original | conditional read original
  | tailValue read original | valueDiscard read original
  | matching read original | matched read original
  | bitNotting read original | bitNotted read original | projectedBitNotted read original
  | forLoop read original | forBoundary read original | breaking read original | continuing read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
  | boundary read outside =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside

private theorem loop_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope
      [shape.loop.id, shape.statement.id] code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings = [] ∧
      tree.children.map (·.expression) =
        [shape.conditionRead.node.id, shape.loopCall.value.node.id, shape.stop.node.id, shape.finalCall.value.node.id] := by
  cases tree with
  | whileLoop read form _ child generated conditionType inner remaining =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
      have inside : inner.closed = true ∧ inner.bindings = [] ∧
          inner.children.map (·.expression) = [shape.loopCall.value.node.id, shape.stop.node.id] :=
        assignment_details inner ready.1 reader shape.assignmentFound shape.assignmentForm
          (shape.local_assignable nodes) (fun remaining ready =>
            assignment_details remaining ready reader shape.flagAssignmentFound shape.flagAssignmentForm
              (shape.flag_assignable nodes) (fun remaining _ => by cases remaining; exact ⟨rfl, rfl, rfl⟩))
      have tail := remaining.at_return reader shape.statementFound shape.statementForm
      have tailChildren := returning_children remaining reader shape.statementFound shape.statementForm
      simp only [Tree.closed, inside.1, tail.1, Bool.and_self, Tree.bindings,
        inside.2.1, tail.2.1, List.nil_append, Tree.children, List.map_cons, List.map_append,
        inside.2.2, tailChildren, List.cons_append, List.nil_append, and_self]
  | initialized read form | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | projectedAssigned read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      simp only [shape.loopForm, expanded] at outside
      cases outside

/-- The exact accepted two declarations, loop writes and return retain their
ordered expression occurrences and both original lexical binders. -/
theorem MethodShape.compiler_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope shape.body code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.saved, shape.flag] ∧
      tree.children.map (·.expression) = shape.childIds := by
  cases tree with
  | initialized read form _ projected child generated childType remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
      cases remaining with
      | initialized read form _ projected child generated childType remaining allocated =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          rw [shape.flagInitializedForm] at form
          cases form
          have tail := loop_details shape nodes remaining ready reader
          simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2.1,
            List.map_nil, Tree.children, tail.2.2, MethodShape.childIds, and_self]
      | absent read form | returning read form | returnUnit read form
      | assigning read form | assigned read form | projectedAssigned read form | whileLoop read form
      | discard read form | block read form | conditional read form
      | valueDiscard read form
      | matching read form | matched read form
      | bitNotting read form | bitNotted read form | projectedBitNotted read form
      | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          rw [shape.flagInitializedForm] at form
          cases form
      | boundary read outside accepted =>
          have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.flagInitializedFound)
          cases same
          simp only [shape.flagInitializedForm, expanded] at outside
          cases outside
  | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | projectedAssigned read form | whileLoop read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      simp only [shape.initializedForm, expanded] at outside
      cases outside


omit nodes

def MethodShape.Reached (id : ExpressionId) : Prop :=
  id ∈ [shape.initialRead.node.id, shape.call.value.node.id, shape.initialFlag.node.id,
    shape.conditionRead.node.id, shape.loopRead.node.id, shape.loopCall.value.node.id,
    shape.stop.node.id, shape.finalRead.node.id, shape.finalCall.value.node.id]

theorem MethodShape.reached_forms : ReachedForms function.typedBody shape.Reached := by
  intro id node reached found
  simp only [Reached, List.mem_cons, List.not_mem_nil, or_false] at reached
  rcases reached with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [shape.initialRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.initialRead.form ▸ LeafForm.read _ _)
  · rw [shape.call.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.call.form⟩
  · rw [shape.initialFlag.found] at found
    cases Option.some.inj found
    exact .inl (shape.initialFlagForm ▸ LeafForm.literal (.bool "true" true))
  · rw [shape.conditionRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.conditionRead.form ▸ LeafForm.read _ _)
  · rw [shape.loopRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.loopRead.form ▸ LeafForm.read _ _)
  · rw [shape.loopCall.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.loopCall.form⟩
  · rw [shape.stop.found] at found
    cases Option.some.inj found
    exact .inl (shape.stopForm ▸ LeafForm.literal (.bool "false" false))
  · rw [shape.finalRead.found] at found
    cases Option.some.inj found
    exact .inl (shape.finalRead.form ▸ LeafForm.read _ _)
  · rw [shape.finalCall.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, _, shape.finalCall.form⟩

include nodes in
theorem MethodShape.reached_arguments : ReachedArguments function.typedBody shape.Reached := by
  intro id node _ found callee arguments instantiation form argument member
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.initialRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]
  · rw [shape.initialFlagForm] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopRead.form] at form; cases form
  · rw [shape.loopCall.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.loopCall.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.calleeForm] at form; cases form
  · have same := (ExpressionForm.call.inj (form.symm.trans shape.finalCall.form)).2.1
    rw [same] at member
    cases List.mem_singleton.mp member
    simp [Reached]

include nodes in
theorem MethodShape.direct_coverage {directRows : List SourceSpecialization.SpecializedFunction}
    (first : DirectSite directRows shape.call.instantiation)
    (loop : DirectSite directRows shape.loopCall.instantiation)
    (last : DirectSite directRows shape.finalCall.instantiation) :
    ∀ id node, function.typedBody.lookupExpression? id = some node →
      ∀ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) → DirectSite directRows instantiation := by
  intro id node found callee arguments instantiation form
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.initialRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.call.form)).2.2)
    exact same ▸ first
  · rw [shape.initialFlagForm] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopRead.form] at form; cases form
  · rw [shape.loopCall.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.loopCall.form)).2.2)
    exact same ▸ loop
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.calleeForm] at form; cases form
  · have same := CallResolution.declaration.inj ((ExpressionForm.call.inj (form.symm.trans shape.finalCall.form)).2.2)
    exact same ▸ last

include nodes in
private theorem method_details_transport {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statements : List StatementId}
    (roots : statements = shape.body)
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope statements code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.saved, shape.flag] ∧
      tree.children.map (·.expression) = shape.childIds := by
  subst statements
  exact shape.compiler_details nodes tree ready reader

/-- The complete method Source certificate comes from the same cached body and
final-plan selector. The finite shape only identifies original source nodes. -/
theorem method_compiler_admission
    {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
    (cached : CallablePreparedMethodSelection.Cached compiled method.specialized)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) method.specialized.parameterSubstitution)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    {signature : ProgramFunctionSignature}
    (shape : MethodShape cached.named.specialized.function signature cached.named.specialized.function.inferredBodyType)
    (nodes : cached.named.specialized.function.typedBody.nodes = shape.nodeList)
    (noLocals : compiled.indexed.base.locals.bindings = [])
    (first : DirectSite table.rows shape.call.instantiation)
    (loop : DirectSite table.rows shape.loopCall.instantiation)
    (last : DirectSite table.rows shape.finalCall.instantiation) :
    Nonempty (CallableIndexedOwnedPreparedScopedMethodAdmission.SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨receipt, ready⟩ := AcceptedMethodBodyReceipts.of_cached cached
  have bodyEq : cached.compilation.statements = shape.body := by
    rw [← AcceptedMethodBodyAdmission.roots cached]
    simp only [AcceptedMethodBodyReceipts.source, CallableIndexedNamedGeneration.source,
      CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.statements, shape.roots,
      List.filterMap_cons, List.filterMap_nil, MethodShape.body]
  have details := method_details_transport shape nodes bodyEq receipt.tree ready (AcceptedMethodBodyReceipts.read cached)
  apply AcceptedMethodBodyAdmission.of_selection cached checked selected parameters range wellFormed table receipt
    (shape.direct_source nodes) (shape.metadata nodes cached.named noLocals)
    (shape.direct_coverage nodes first loop last) shape.reached_forms (shape.reached_arguments nodes)
  · intro id _ ⟨initializer⟩
    have found := initializer.found
    simp only [noLocals, List.find?_nil, Option.filter_none] at found
    cases found
  · intro child member
    have present := (congrArg (fun ids => child.expression ∈ ids) details.2.2).mp
      (List.mem_map_of_mem member)
    simp only [MethodShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same | same | same | same | same
    all_goals simp [MethodShape.Reached, same]
  · exact details.1
  · intro binding member
    have present := (congrArg (fun binders => binding.binder ∈ binders) details.2.1).mp
      (List.mem_map_of_mem member)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · rw [same, shape.savedScheme]; rfl
    · rw [same, shape.flagScheme]; rfl

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceMethodSupport
/-! Actual operator selections retain the complete specialized method source and
its synthetic signature. The finite cached table supplies scoped syntax without
erasing the implementation substitution; SourceAt supplies independent typing. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure MethodSource (fixture : CompiledFixture) (source : TypedSource) (resultType : TypeSystem.Ty) where
  function : CheckedFunction
  signature : ProgramFunctionSignature
  shape : MethodShape function signature resultType
  sameSource : source = function.typedBody
  nodes : function.typedBody.nodes = shape.nodeList
  generic : shape.generic = fixture.identitySignature
  parameter : shape.genericParameter = fixture.identityParameter
  trait : shape.trait = .declaration fixture.mark.id
  scalar : resultType = .word ∨ resultType = .bool

private def observeMethodSource (fixture : CompiledFixture) (method : ExecutableImplMethods.CheckedMethod) :
    IO (MethodSource fixture method.specialized.function.typedBody method.specialized.function.inferredBodyType) := do
  let function := method.specialized.function
  let signature := method.synthetic
  let ⟨shape, generic, parameter, sameTrait⟩ ← observeMethod function signature
    function.inferredBodyType fixture.identitySignature fixture.identityParameter (.declaration fixture.mark.id)
  let ⟨scalar⟩ ← observed (function.inferredBodyType = .word ∨ function.inferredBodyType = .bool) "method scalar result"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = shape.nodeList) "actual specialized method nodes"
  return ⟨function, signature, shape, rfl, nodes, generic, parameter, sameTrait, scalar⟩

private def MethodRowCase (fixture : CompiledFixture) (named : SourceCoreGeneralFunctions.Function) : Prop :=
  (∀ definition ∈ (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner) ∨
  Nonempty (MethodSource fixture named.specialized.function.typedBody named.specialized.function.inferredBodyType)

structure MethodBodies (fixture : CompiledFixture) : Prop where
  bodies : ∀ named ∈ fixture.recipe.compiled.indexed.base.functions, MethodRowCase fixture named

private def observeSelectedMethod (fixture : CompiledFixture)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode) :
    IO ExecutableImplMethods.CheckedMethod := do
  let available ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      fixture.recipe.compiled.sourceProgram caller.key caller.assumptions with
    | .ok available => pure available
    | .error error => throw (IO.userError (reprStr error))
  let .unary operator _ := node.form | throw (IO.userError "method selector unary node")
  match SourceCompilationPlan.checkedUnaryOperatorMethod fixture.recipe.compiled.sourceProgram caller node available operator with
  | .ok selection => pure selection.method
  | .error error => throw (IO.userError (reprStr error))

private def observeMethodBodyList (fixture : CompiledFixture)
    (word bool : ExecutableImplMethods.CheckedMethod)
    (wordSource : MethodSource fixture word.specialized.function.typedBody word.specialized.function.inferredBodyType)
    (boolSource : MethodSource fixture bool.specialized.function.typedBody bool.specialized.function.inferredBodyType) :
    (named : List SourceCoreGeneralFunctions.Function) → IO (PLift (∀ row ∈ named, MethodRowCase fixture row))
  | [] => pure ⟨by intro row member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← (do
      if nonMethod : (Program.ofChecked fixture.recipe.compiled.sourceProgram).methods.all
          (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        return ⟨Or.inl (by intro definition member; exact of_decide_eq_true (List.all_eq_true.mp nonMethod definition member))⟩
      else if same : (first.specialized == word.specialized) = true then
        have equal : first.specialized = word.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨wordSource⟩)⟩
      else if same : (first.specialized == bool.specialized) = true then
        have equal : first.specialized = bool.specialized := eq_of_beq same
        return ⟨Or.inr (equal ▸ ⟨boolSource⟩)⟩
      else throw (IO.userError "actual cached method specialization missing") : IO (PLift (MethodRowCase fixture first)))
    let ⟨tail⟩ ← observeMethodBodyList fixture word bool wordSource boolSource rest
    return ⟨by
      intro row member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail row member⟩

def observeMethodBodies (fixture : CompiledFixture) : IO (PLift (MethodBodies fixture)) := do
  let program ← observeProgram fixture
  let word ← observeSelectedMethod fixture program.relayWordRow.row program.relayWordShape.call.value.node
  let bool ← observeSelectedMethod fixture program.relayBoolRow.row program.relayBoolShape.call.value.node
  let wordSource ← observeMethodSource fixture word
  let boolSource ← observeMethodSource fixture bool
  let ⟨bodies⟩ ← observeMethodBodyList fixture word bool wordSource boolSource fixture.recipe.compiled.indexed.base.functions
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

/-- The original selected method table has references and genuine declaration calls. -/
theorem MethodBodies.no_lambda {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨original⟩ := bodies.selected principal
  rw [original.sameSource] at found
  rcases original.shape.direct_source original.nodes id node found with ⟨name, binder, read⟩ | ⟨name, value, instantiation, read⟩ <;>
    rw [read] at form <;> cases form

private theorem row_record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered_variant {plan : SourceCompilationPlan.Plan}
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

private theorem MethodSource.target {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.identityWordRow.row ∨
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation observed.identityBoolRow.row := by
  have exactCall : instantiation = ⟨fixture.identitySignature.id, [(fixture.identityParameter, resultType)],
      .function resultType resultType, [predicate (.declaration fixture.mark.id) resultType],
      fixture.identitySignature.parameterComptime, fixture.identitySignature.returnComptime⟩ := by
    rcases site with rfl | rfl | rfl
    all_goals simp only [original.shape.call.exact, original.shape.loopCall.exact, original.shape.finalCall.exact,
      original.generic, original.parameter, original.trait, predicate, SourceCoreEvidenceMethod.predicate]
  rcases original.scalar with word | bool
  · exact .inl (exactCall.trans (word ▸ observed.identityWordInstantiation.symm))
  · exact .inr (exactCall.trans (bool ▸ observed.identityBoolInstantiation.symm))

private theorem MethodSource.supported {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation) :
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported fixture.recipe.compiled.indexed.base.plan instantiation := by
  rcases original.target observed site with word | bool
  · rw [word]
    refine ⟨?_, retained_ordered_variant observed.identityWordRow.target (row_record observed.identityWordRow)⟩
    intro parameter replacement member
    rw [observed.identityWordInstantiation] at member
    cases List.mem_singleton.mp member
    rfl
  · rw [bool]
    refine ⟨?_, retained_ordered_variant observed.identityBoolRow.target (row_record observed.identityBoolRow)⟩
    intro parameter replacement member
    rw [observed.identityBoolInstantiation] at member
    cases List.mem_singleton.mp member
    rfl

private theorem MethodSource.covered {fixture : CompiledFixture} {source : TypedSource} {resultType : TypeSystem.Ty}
    (original : MethodSource fixture source resultType) (observed : ObservedProgram fixture)
    (inventory : OrdinaryInventory fixture observed)
    {instantiation : DeclarationInstantiation} (site : original.shape.DirectSites instantiation)
    (index : Nat) (signature : SourceCoreCalls.Signature)
    (target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan instantiation = .ok signature.key)
    (global : fixture.recipe.compiled.indexed.base.globals[index]? = some signature) :
    ∃ header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows,
      header.slot = index ∧ header.named.signature = signature := by
  rcases original.target observed site with word | bool
  · rw [word, observed.identityWordRow.target] at target
    obtain ⟨rfl, rfl⟩ := observed.identityWordRow.global_slot global (Except.ok.inj target).symm
    exact ⟨inventory.identityWordHeader.header, inventory.identityWord_member, inventory.identityWordSlot, inventory.identityWordSignature⟩
  · rw [bool, observed.identityBoolRow.target] at target
    obtain ⟨rfl, rfl⟩ := observed.identityBoolRow.global_slot global (Except.ok.inj target).symm
    exact ⟨inventory.identityBoolHeader.header, inventory.identityBool_member, inventory.identityBoolSlot, inventory.identityBoolSignature⟩

/-- The exact accepted method flow and real SourceAt issue the scoped packet.
No method execution is assumed by this static construction. -/
theorem MethodBodies.support {fixture : CompiledFixture} (bodies : MethodBodies fixture)
    (observed : ObservedProgram fixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial fixture.recipe.compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      fixture.recipe.compiled.sourceProgram principal.named.specialized principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (inventory : OrdinaryInventory fixture observed)
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodies.Support principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows) stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨original⟩ := bodies.selected principal
  have statements : principal.cached.compilation.statements = original.shape.body := by
    have roots : (principal.sourceBody.source.roots.filterMap fun root => match root with
        | .statement statement => some statement | .expression _ => none) = principal.cached.compilation.statements :=
      principal.source_frame.roots.filterMap_eq
    rw [original.sameSource, original.shape.roots] at roots
    simpa [MethodShape.body] using roots.symm
  have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape principal.sourceBody.source true
      principal.cached.compilation.statements := by
    rw [original.sameSource, statements]
    exact original.shape.body_shape
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Packet principal :=
    ⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩
  refine ⟨.scoped packet, rfl, ?_⟩
  change CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Support principal packet (CallableIndexedOwnedPreparedFiniteNamedInventories.headers inventory.rows) stages _
  have sourceForms : CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.DirectSource principal.sourceBody.source := by
    rw [original.sameSource]
    exact original.shape.direct_source original.nodes
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed principal.named principal.sourceBody.source original.shape.DirectSites := by
    simpa only [original.sameSource] using
      (original.shape.metadata (directSites := original.shape.DirectSites) original.nodes principal.named observed.noLocals)
  apply CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.of_actual_with_evidence principal packet diagnostic receiver
    fixture.source_wellFormed sourceForms (fun _ site => original.supported observed site) metadata
    inventory.rows (fun _ site index signature target global => original.covered observed inventory site index signature target global)
    resolved fixture.recipePrepared observed.wordRow.entryMember
  obtain ⟨final, facts, bodyTyped, _complete⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet fixture.source_wellFormed
  have unique := sourceAt.unique
  rw [original.sameSource] at unique
  simp only [original.sameSource, statements] at bodyTyped ⊢
  exact (original.shape.body_syntax original.nodes unique original.shape.children bodyTyped).prepared

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceRelaySyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (NoIndirectSource)
private theorem returning_variant {source : TypedSource} {context final : SourceSemantics.Context}
    {resultType : TypeSystem.Ty} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (expression : ExpressionNode)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = resultType)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression.id))
    (annotation : node.type = resultType) (leaf : approved expression.id)
    (typed : StatementHasType source {returnType := resultType} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) resultType := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation expressionFound expressionType
        (by simpa only [expressionType] using value) leaf)

section Metadata
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedRelayShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)
include nodes in
theorem SelectedRelayShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.call.value.node ∨ node = shape.conditionRead.node ∨ node = shape.loopSecondRead.node ∨ node = shape.loopCall.value.node ∨ node = shape.stop.node ∨ node = shape.finalRead.node ∨ node = shape.finalCall.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedRelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present
include nodes in
theorem SelectedRelayShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopSecondRead.form] at form; cases form
  · rw [shape.loopCall.form] at form; cases form
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.form] at form; cases form

include nodes in
theorem SelectedRelayShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.call.form]; trivial)))
    · exact .inl shape.conditionRead.requirements
    · exact .inl shape.loopSecondRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.loopCall.form]; trivial)))
    · exact .inl shape.stop.requirements
    · exact .inl shape.finalRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.finalCall.form]; trivial)))
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.call.value.coercions
    · exact shape.conditionRead.coercions
    · exact shape.loopSecondRead.coercions
    · exact shape.loopCall.value.coercions
    · exact shape.stop.coercions
    · exact shape.finalRead.coercions
    · exact shape.finalCall.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]
end Metadata
section Factory
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedRelayShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedRelayShape.local_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.localBinder.id = .ok shape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedRelayShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm,
    shape.localOwner, shape.localScheme, TypeSystem.Scheme.mono, shape.localRequirements, Ne.symm shape.localFirst, Ne.symm shape.localSecond, Ne.symm shape.localFlag]

include nodes in
theorem SelectedRelayShape.flag_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.flag.id = .ok shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedRelayShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm,
    shape.flagOwner, shape.flagScheme, TypeSystem.Scheme.mono, shape.flagRequirements, Ne.symm shape.flagFirst, Ne.symm shape.flagSecond, shape.localFlag]

theorem SelectedRelayShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true shape.body :=
  .initialized shape.initializedFound shape.initializedForm
    (.whileLoop shape.loopFound shape.loopForm
      (.assign shape.assignmentFound shape.assignmentForm (.inl rfl) shape.targetBare
        (.assign shape.flagAssignmentFound shape.flagAssignmentForm (.inl rfl) shape.flagTargetBare .nil))
      (.returnValue [] shape.statementFound shape.statementForm))

def SelectedRelayShape.childIds : List ExpressionId :=
  [shape.call.value.node.id, shape.conditionRead.node.id, shape.loopCall.value.node.id,
    shape.stop.node.id, shape.finalCall.value.node.id]

include nodes in
theorem SelectedRelayShape.body_syntax
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ shape.childIds, approved id)
    (typed : StatementsHaveType function.typedBody {returnType := type}
      context shape.body final facts) :
    GenericImperativeMatch.Syntax function.typedBody approved context
      (.statements true shape.body) type := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax shape.initializedFound shape.initializedForm
    (shape.local_declaration nodes) shape.localScheme
    (by simp [shape.inputs, Ne.symm shape.localFirst, Ne.symm shape.localSecond, Ne.symm shape.localFlag])
    shape.call.value.found shape.call.value.type (leaves _ (by simp [childIds]))
    (form_at unique shape.initializedFound initialized)
  obtain ⟨middle, _, _, first, suffix⟩ := head_tail tail
  have firstForm := form_at unique shape.loopFound first
  rw [shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop shape.loopFound shape.loopForm
      shape.conditionRead.found shape.conditionRead.type
      (by simpa only [shape.conditionRead.type] using conditionTyped) (leaves _ (by simp [childIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique shape.assignmentFound assignedHead
      rw [shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned shape.loopCall.value.node shape.loopCall.value.found shape.loopCall.value.type
          shape.assignmentFound shape.assignmentForm
          (by rw [shape.targetRoot]; exact shape.local_declaration nodes)
          shape.localScheme shape.targetBare shape.targetType
          (leaves _ (by simp [childIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique shape.flagAssignmentFound flagHead
        rw [shape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned shape.stop.node shape.stop.found shape.stop.type
            shape.flagAssignmentFound shape.flagAssignmentForm
            (by rw [shape.flagTargetRoot]; exact shape.flag_declaration nodes)
            shape.flagScheme shape.flagTargetBare shape.flagTargetType
            (leaves _ (by simp [childIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail suffix
      exact returning_variant unique shape.finalCall.value.node shape.finalCall.value.found shape.finalCall.value.type
        shape.statementFound shape.statementForm shape.statementType (leaves _ (by simp [childIds])) returningHead
end Factory
theorem SelectedRelayShape.children {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedRelayShape function type) :
    ∀ id ∈ shape.childIds, GeneralSyntax function.typedBody id (fun _ => False) := by
  intro id member
  simp only [SelectedRelayShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .unary shape.call.value.found shape.call.form (.leaf (.read shape.firstRead.found shape.firstRead.form))
  · exact .leaf (.read shape.conditionRead.found shape.conditionRead.form)
  · exact .unary shape.loopCall.value.found shape.loopCall.form (.leaf (.read shape.loopSecondRead.found shape.loopSecondRead.form))
  · exact .leaf (.literal shape.stop.found (shape.stopForm ▸ .bool _ _))
  · exact .unary shape.finalCall.value.found shape.finalCall.form (.leaf (.read shape.finalRead.found shape.finalRead.form))

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceRelayCompilerSupport
/-! Original relay observations identify every source expression. The eventual
body admission follows the actual compiler tree and its ordered child actions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow AcceptedNamedBodyFlow

variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedRelayShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes

/-- Every original stored expression is a leaf or one of the three method
operator occurrences, with its original nonempty requirement list. -/
theorem SelectedRelayShape.compiler_form {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    LeafForm node.form ∨
      (∃ operand, node.form = .unary .bitNot operand ∧ node.requirements ≠ []) := by
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same
  all_goals subst node
  · exact .inl (shape.firstRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.call.form, by rw [shape.call.requirements]; simp⟩
  · exact .inl (shape.conditionRead.form ▸ LeafForm.read _ _)
  · exact .inl (shape.loopSecondRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.loopCall.form, by rw [shape.loopCall.requirements]; simp⟩
  · exact .inl (shape.stopForm ▸ LeafForm.literal (.bool "false" false))
  · exact .inl (shape.finalRead.form ▸ LeafForm.read _ _)
  · exact .inr ⟨_, shape.finalCall.form, by rw [shape.finalCall.requirements]; simp⟩

theorem SelectedRelayShape.no_direct {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation)) : False := by
  rcases shape.compiler_form nodes found with leaf | ⟨operand, unary, _⟩
  · rw [form] at leaf
    cases leaf with
    | literal atomic => cases atomic
  · rw [unary] at form
    cases form


theorem SelectedRelayShape.compiler_forms :
    ReachedMethodForms function.typedBody (fun _ => True) := by
  intro id node _ found
  rcases shape.compiler_form nodes found with leaf | ⟨operand, form, _⟩
  · exact .inl leaf
  · exact .inr (.inr (.inr (.inl ⟨_, _, form⟩)))

theorem SelectedRelayShape.compiler_requirements :
    ReachedMethodRequirements function.typedBody (fun _ => True) := by
  intro id node _ found method
  rcases shape.compiler_form nodes found with leaf | ⟨_, _, requirements⟩
  · rcases method with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    all_goals
      rw [form] at leaf
      cases leaf with
      | literal atomic => cases atomic
  · exact requirements

theorem SelectedRelayShape.local_assignable :
    Assignable function.typedBody shape.resolution .equal := by
  refine ⟨.inl rfl, shape.targetBare, ?_⟩
  intro binder found
  rw [shape.targetRoot, shape.local_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.localScheme, shape.targetType]
  rfl

theorem SelectedRelayShape.flag_assignable :
    Assignable function.typedBody shape.flagResolution .equal := by
  refine ⟨.inl rfl, shape.flagTargetBare, ?_⟩
  intro binder found
  rw [shape.flagTargetRoot, shape.flag_declaration nodes] at found
  cases Except.ok.inj found
  rw [shape.flagScheme, shape.flagTargetType]
  rfl

omit nodes in
private theorem assignment_details_variant {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {statement : StatementNode} {assignment : AssignmentResolution} {expression : ExpressionId}
    {rest : List StatementId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope (statement.id :: rest) code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .assignValue assignment .equal expression)
    (assignable : Assignable source assignment .equal)
    (tail : ∀ {fuel scope code},
      (remaining : Tree policy source result reasonAt mode escaped fuel scope rest code) →
      remaining.Ready → remaining.closed = true ∧ remaining.bindings = []) :
    tree.closed = true ∧ tree.bindings = [] := by
  cases tree with
  | assigning read original _ remaining assigned =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (ready.1 (.inl assignable))
  | projectedAssigned read original _ remaining receipt route =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at original
      cases original
      exact False.elim (receipt.projected assignable.2.1)
  | assigned read original _ remaining receipt targetType =>
      exact tail remaining ready
  | initialized read original | absent read original | returning read original
  | returnUnit read original | whileLoop read original
  | discard read original | block read original | conditional read original
  | tailValue read original | valueDiscard read original
  | matching read original | matched read original
  | bitNotting read original | bitNotted read original | projectedBitNotted read original
  | forLoop read original | forBoundary read original | breaking read original | continuing read original =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside


private theorem loop_details_variant {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope
      [shape.loop.id, shape.statement.id] code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings = [] := by
  cases tree with
  | whileLoop read form _ child generated conditionType inner remaining =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
      have inside : inner.closed = true ∧ inner.bindings = [] :=
        assignment_details_variant inner ready.1 reader shape.assignmentFound shape.assignmentForm
          (shape.local_assignable nodes) (fun remaining ready =>
            assignment_details_variant remaining ready reader shape.flagAssignmentFound shape.flagAssignmentForm
              (shape.flag_assignable nodes) (fun remaining _ => by cases remaining; exact ⟨rfl, rfl⟩))
      have tail := remaining.at_return reader shape.statementFound shape.statementForm
      simp only [Tree.closed, inside.1, tail.1, Bool.and_self, Tree.bindings,
        inside.2, tail.2.1, List.nil_append, and_self]
  | initialized read form | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | projectedAssigned read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      rw [shape.loopForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.loopFound)
      cases same
      simp only [shape.loopForm, expanded] at outside
      cases outside

/-- Inverting the original accepted let, loop, two writes and return closes
this exact compiler tree and identifies its only declaration. -/
theorem SelectedRelayShape.compiler_details {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    (tree : Tree policy function.typedBody result reasonAt mode escaped fuel scope shape.body code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.localBinder] := by
  cases tree with
  | initialized read form _ projected child generated childType remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
      have tail := loop_details_variant shape nodes remaining ready reader
      simp only [Tree.closed, Tree.bindings, List.map_cons, tail.1, tail.2,
        List.map_nil, and_self]
  | absent read form | returning read form | returnUnit read form
  | assigning read form | assigned read form | projectedAssigned read form | whileLoop read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      rw [shape.initializedForm] at form
      cases form
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans shape.initializedFound)
      cases same
      simp only [shape.initializedForm, expanded] at outside
      cases outside


omit nodes in
private theorem details_transport {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {result : Ty} {reasonAt : ExpressionId → Word}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {source : TypedSource} {statements : List StatementId}
    (sourceEq : source = function.typedBody) (roots : statements = shape.body)
    (nodes : function.typedBody.nodes = shape.nodeList)
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (ready : tree.Ready)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [shape.localBinder] := by
  subst source statements
  exact shape.compiler_details nodes tree ready reader


omit nodes

section Header
variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {row : ObservedRow fixture signature}

/-- The original metadata check and the accepted compiler tree together issue
this Header's scoped source certificate. -/
theorem ActualHeader.relay_compiler_admission
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows))
    (metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) = some ⟨metadata⟩)
    (supported : ∀ instantiation, CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = shape.body := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have checked : ∃ receipt : PLift
      (CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
        (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows)),
      CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
        fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
        (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite directRows) = some receipt := by
    rw [namedEq, actual.source]
    exact ⟨⟨metadata⟩, metadataAccepted⟩
  obtain ⟨⟨actualMetadata⟩, actualAccepted⟩ := checked
  obtain ⟨receipt, ready⟩ := AcceptedNamedBodyRefinement.of_header actual.prepared actual.aligned
  have details := details_transport shape actual.source bodyEq nodes receipt.tree ready
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
  refine AcceptedNamedRefinedBodyAdmission.of_receipt actual.prepared actual.aligned receipt actualMetadata
    supported ?_ details.1 ?_ ?_ fixture.source_wellFormed
  · intro id node found callee arguments instantiation form
    rw [actual.source] at found
    exact False.elim (shape.no_direct nodes found form)
  · intro binding member
    have present := List.mem_map.mpr
      (show ∃ actual ∈ receipt.tree.bindings, actual.binder = binding.binder from ⟨binding, member, rfl⟩)
    rw [details.2] at present
    have same := List.mem_singleton.mp present
    rw [same, shape.localScheme]
    rfl
  · intro child _member ⟨residual⟩
    exact residual.impossible_methods actualMetadata
      (reached := fun _ => True)
      (by rw [actual.source]; exact shape.compiler_forms nodes)
      (fun id _ initializer => by
        obtain ⟨initializer⟩ := initializer
        have found := initializer.found
        simp only [noLocals, List.find?_nil, Option.filter_none] at found
        cases found)
      ⟨⟨fun _ _ _ _ _ _ _ _ _ _ => True.intro,
        fun _ _ _ _ _ _ _ _ => ⟨True.intro, fun _ _ => True.intro⟩⟩,
        fun _ _ _ _ _ _ _ => True.intro,
        fun _ _ _ _ _ _ _ _ => ⟨True.intro, True.intro⟩⟩
      (ReachedMethodMetadata.of_accepted actualAccepted)
      (by rw [actual.source]; exact shape.compiler_requirements nodes)
      True.intro
end Header

end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20

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
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedFunctionCall first.completion.session observed.boolRow.row.key [.bool false, .bool true, .bool true]
  secondType : second.handle.sourceType = closureType .bool
  firstRead : ObservedCall second.completion.session observed.useWordRow.row.key [.function first.handle]
  firstValue : firstRead.completion.value = .word (Core.Word.ofNatModulo 33)
  third : ObservedFunctionCall firstRead.completion.session observed.wordRow.row.key [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  thirdType : third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedCall third.completion.session observed.useBoolRow.row.key [.function second.handle]
  secondValue : secondRead.completion.value = .bool true
  repeatedRead : ObservedCall secondRead.completion.session observed.useWordRow.row.key [.function first.handle]
  repeatedValue : repeatedRead.completion.value = .word (Core.Word.ofNatModulo 33)
  thirdRead : ObservedCall repeatedRead.completion.session observed.useWordRow.row.key [.function third.handle]
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 55)
  heapSizes : [first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [13,40,67,149,176,258,340,403]

def observeSequence (fixture : CompiledFixture) (program : ObservedProgram fixture) :
    IO (ObservedSequence fixture program) := do
  let first ← observePublicRun fixture program.wordRow.toObservedRow
  let second ← observeFunctionCall first.completion.session program.boolRow.row.key [.bool false, .bool true, .bool true]
  let ⟨secondType⟩ ← observed (second.handle.sourceType = closureType .bool) "second public handle type"
  let firstRead ← observeCall second.completion.session program.useWordRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← observed (firstRead.completion.value = .word (Core.Word.ofNatModulo 33)) "first compiled indirect output"
  let third ← observeFunctionCall firstRead.completion.session program.wordRow.row.key [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  let ⟨thirdType⟩ ← observed (third.handle.sourceType = closureType .word) "third public handle type"
  let ⟨firstSecond⟩ ← observed (first.handle ≠ second.handle) "first/second handles distinct"
  let ⟨firstThird⟩ ← observed (first.handle ≠ third.handle) "first/third handles distinct"
  let ⟨secondThird⟩ ← observed (second.handle ≠ third.handle) "second/third handles distinct"
  let secondRead ← observeCall third.completion.session program.useBoolRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← observed (secondRead.completion.value = .bool true) "Bool compiled indirect output"
  let repeatedRead ← observeCall secondRead.completion.session program.useWordRow.row.key [.function first.handle]
  let ⟨repeatedValue⟩ ← observed (repeatedRead.completion.value = .word (Core.Word.ofNatModulo 33)) "retained first compiled indirect output"
  let thirdRead ← observeCall repeatedRead.completion.session program.useWordRow.row.key [.function third.handle]
  let ⟨thirdValue⟩ ← observed (thirdRead.completion.value = .word (Core.Word.ofNatModulo 55)) "third compiled indirect output"
  let ⟨heapSizes⟩ ← observed ([first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [13,40,67,149,176,258,340,403]) "exact seven-session heap sequence"
  return {first, second, secondType, firstRead, firstValue, third, thirdType, firstSecond, firstThird, secondThird, secondRead, secondValue, repeatedRead, repeatedValue, thirdRead, thirdValue, heapSizes}
end Tests.SourceCoreMethodOriginEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodOriginEvidenceCommon
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
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
  RecursiveNamedPublicPhysicalSessionState.State inventory.rows inventory.wordHeader.header
    receiver.completion observed.profile fixture.recipe publicSession entries

abbrev SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall inventory.wordHeader.header header
    invocation before arguments outcome after

theorem word_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (value next : Core.Word) (flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word, .word, .bool]
      [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
  exact .cons (.data
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
    ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩)
    (.cons (.data
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
      (.cons (.data
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil))

theorem word_simple (value next : Core.Word) (flag : Bool) :
    ∀ item ∈ ([.word value, .word next, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .word value
  · exact .word next
  · exact .bool flag

theorem bool_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (value next flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.bool, .bool, .bool]
      [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
  exact .cons (.data
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩
    ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩)
    (.cons (.data
      ⟨.bool next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool next⟩
      ⟨.bool next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool next⟩)
      (.cons (.data
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil))

theorem bool_simple (value next flag : Bool) :
    ∀ item ∈ ([.bool value, .bool next, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic item := by
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .bool value
  · exact .bool next
  · exact .bool flag

end Tests.SourceCoreMethodOriginEvidence
end
