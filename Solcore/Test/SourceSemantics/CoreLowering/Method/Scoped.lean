import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Direct
import Solcore.Test.SourceSemantics.CoreLowering.Method.Closure
import Solcore.Test.SourceSemantics.CoreLowering.Evidence.Scoped
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootCoverage
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalClosureAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Scoped method tests

Scoped methods: source, fixture, selection, metadata and supports.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedResults
set_option autoImplicit false
namespace Tests.SourceCoreMethodScoped
export Tests.SourceCoreEvidenceDirect (ScalarOutput)
end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedSource
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodScoped
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

structure SelectedFactoryShape (function : CheckedFunction) (type : TypeSystem.Ty) where
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
  firstOwner : first.id.owner = function.typedBody.owner
  secondOwner : second.id.owner = function.typedBody.owner
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

def SelectedFactoryShape.body {function type}
    (shape : SelectedFactoryShape function type) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def SelectedFactoryShape.nodeList {function type}
    (shape : SelectedFactoryShape function type) : List Node :=
  [.expression shape.firstRead.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.conditionRead.node, .expression shape.loopSecondRead.node,
   .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.value.node, .statement shape.statement,
   .expression shape.expression.node, .statement shape.outerReturn]


def observeSelectedFactory (function : CheckedFunction) (type : TypeSystem.Ty) :
    IO (SelectedFactoryShape function type) := do
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
  let ⟨firstOwner⟩ ← observed (first.id.owner = function.typedBody.owner) "factory firstOwner"
  let ⟨secondOwner⟩ ← observed (second.id.owner = function.typedBody.owner) "factory secondOwner"
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
  return {expression, outerReturn, lambda, outerReturnFound, outerReturnForm, outerReturnType, first, second, flag, localBinder, firstRead, call, initialized, conditionRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalCall, statement, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, firstOwner, secondOwner, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  makeWordRow : ObservedRow fixture fixture.makeSignature
  makeBoolRow : ObservedRow fixture fixture.makeSignature
  useWordRow : ObservedRoot fixture fixture.useWordSignature
  useBoolRow : ObservedRoot fixture fixture.useBoolSignature
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  makeWordShape : SelectedFactoryShape makeWordRow.row.function .word
  makeBoolShape : SelectedFactoryShape makeBoolRow.row.function .bool
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
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row
  ordinarySlotsDistinct : [wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, useWordRow.index, useBoolRow.index].Nodup
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 8
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let makeWordRow ← observeRow fixture fixture.makeSignature [.word]
  let makeBoolRow ← observeRow fixture fixture.makeSignature [.bool]
  let useWordRow ← observeRootRow fixture fixture.useWordSignature
  let useBoolRow ← observeRootRow fixture fixture.useBoolSignature
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  let makeWordShape ← observeSelectedFactory makeWordRow.row.function .word
  let makeBoolShape ← observeSelectedFactory makeBoolRow.row.function .bool
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
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row) "actual method closure wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row) "actual method closure boolInstantiation"
  let ⟨ordinarySlotsDistinct⟩ ← observed ([wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, useWordRow.index, useBoolRow.index].Nodup) "actual method closure ordinarySlotsDistinct"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 8) "actual method closure globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]) "actual method closure entryKeys"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual method closure noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual method closure profile"
  return {wordRow, boolRow, makeWordRow, makeBoolRow, useWordRow, useBoolRow, wordShape, boolShape, makeWordShape, makeBoolShape, useWordShape, useBoolShape, wordInputScheme, wordNodes, wordResultType, wordKey, boolInputScheme, boolNodes, boolResultType, boolKey, makeWordInputScheme, makeWordNodes, makeWordResultType, makeWordKey, makeBoolInputScheme, makeBoolNodes, makeBoolResultType, makeBoolKey, useWordInputScheme, useWordNodes, useWordResultType, useWordKey, useBoolInputScheme, useBoolNodes, useBoolResultType, useBoolKey, wordInstantiation, boolInstantiation, ordinarySlotsDistinct, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedCatalog
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedClosureSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
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
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedFactoryShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)
include nodes in
theorem SelectedFactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.call.value.node ∨ node = shape.conditionRead.node ∨ node = shape.loopSecondRead.node ∨ node = shape.loopCall.value.node ∨ node = shape.stop.node ∨ node = shape.finalRead.node ∨ node = shape.finalCall.value.node ∨ node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedFactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present
include nodes in
theorem SelectedFactoryShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopSecondRead.form] at form; cases form
  · rw [shape.loopCall.form] at form; cases form
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.form] at form; cases form
  · rw [shape.lambda] at form; cases form

include nodes in
theorem SelectedFactoryShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.call.form]; trivial)))
    · exact .inl shape.conditionRead.requirements
    · exact .inl shape.loopSecondRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.loopCall.form]; trivial)))
    · exact .inl shape.stop.requirements
    · exact .inl shape.finalRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.finalCall.form]; trivial)))
    · exact .inl shape.expression.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.call.value.coercions
    · exact shape.conditionRead.coercions
    · exact shape.loopSecondRead.coercions
    · exact shape.loopCall.value.coercions
    · exact shape.stop.coercions
    · exact shape.finalRead.coercions
    · exact shape.finalCall.value.coercions
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]
end Metadata
section Factory
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedFactoryShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedFactoryShape.local_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.localBinder.id = .ok shape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.localOwner, shape.localScheme, TypeSystem.Scheme.mono, shape.localRequirements, Ne.symm shape.localFirst, Ne.symm shape.localSecond, Ne.symm shape.localFlag]

include nodes in
theorem SelectedFactoryShape.flag_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.flag.id = .ok shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.flagOwner, shape.flagScheme, TypeSystem.Scheme.mono, shape.flagRequirements, Ne.symm shape.flagFirst, Ne.symm shape.flagSecond, shape.localFlag]

include nodes in
theorem SelectedFactoryShape.first_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.first.id = .ok shape.first := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.firstOwner, shape.firstScheme, TypeSystem.Scheme.mono, shape.firstRequirements, shape.different, shape.flagFirst, shape.localFirst]

theorem SelectedFactoryShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true shape.body :=
  .initialized shape.initializedFound shape.initializedForm
    (.whileLoop shape.loopFound shape.loopForm
      (.assign shape.assignmentFound shape.assignmentForm (.inl rfl) shape.targetBare
        (.assign shape.flagAssignmentFound shape.flagAssignmentForm (.inl rfl) shape.flagTargetBare .nil))
      (.returnValue [] shape.statementFound shape.statementForm))

def SelectedFactoryShape.childIds : List ExpressionId :=
  [shape.call.value.node.id, shape.conditionRead.node.id, shape.loopCall.value.node.id,
    shape.stop.node.id, shape.finalCall.value.node.id]

include nodes in
theorem SelectedFactoryShape.body_syntax
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
          (by rw [shape.targetRoot]; exact shape.first_declaration nodes)
          shape.firstScheme shape.targetBare shape.targetType
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
end Factory
theorem SelectedFactoryShape.children {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type) :
    ∀ id ∈ shape.childIds, GeneralSyntax function.typedBody id (fun _ => False) := by
  intro id member
  simp only [SelectedFactoryShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .unary shape.call.value.found shape.call.form (.leaf (.read shape.firstRead.found shape.firstRead.form))
  · exact .leaf (.read shape.conditionRead.found shape.conditionRead.form)
  · exact .unary shape.loopCall.value.found shape.loopCall.form (.leaf (.read shape.loopSecondRead.found shape.loopSecondRead.form))
  · exact .leaf (.literal shape.stop.found (shape.stopForm ▸ .bool _ _))
  · exact .unary shape.finalCall.value.found shape.finalCall.form (.leaf (.read shape.finalRead.found shape.finalRead.form))

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedInventory
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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

def OrdinaryInventory.rows {fixture observed} (given : OrdinaryInventory fixture observed) :
    Inventory [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.useWordInput, given.useBoolInput] :=
  .cons given.wordPacket (.cons given.boolPacket (.cons given.makeWordPacket (.cons given.makeBoolPacket (.cons given.useWordPacket (.cons given.useBoolPacket (.nil))))))

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature⟩ := observed.makeWordRow.issue
  obtain ⟨makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature⟩ := observed.makeBoolRow.issue
  obtain ⟨useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature⟩ := observed.useWordRow.issue
  obtain ⟨useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature⟩ := observed.useBoolRow.issue
  exact ⟨{wordInput, wordSame, wordPacket, wordHeader, wordAligned, wordSlot, wordSignature, boolInput, boolSame, boolPacket, boolHeader, boolAligned, boolSlot, boolSignature, makeWordInput, makeWordSame, makeWordPacket, makeWordHeader, makeWordAligned, makeWordSlot, makeWordSignature, makeBoolInput, makeBoolSame, makeBoolPacket, makeBoolHeader, makeBoolAligned, makeBoolSlot, makeBoolSignature, useWordInput, useWordSame, useWordPacket, useWordHeader, useWordAligned, useWordSlot, useWordSignature, useBoolInput, useBoolSame, useBoolPacket, useBoolHeader, useBoolAligned, useBoolSlot, useBoolSignature}⟩

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

theorem OrdinaryInventory.useWord_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useWordHeader.header ∈ headers given.rows := by
  rw [given.useWordAligned]
  simp [OrdinaryInventory.rows, headers]

theorem OrdinaryInventory.useBool_member {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.useBoolHeader.header ∈ headers given.rows := by
  rw [given.useBoolAligned]
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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
  simpa only [RootShape.nodeList, List.mem_cons, List.mem_singleton,
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
end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedMethodSupport
/-! Every selected method uses the actual original method table. Structural
Source instantiation transports its read-and-return syntax; the real compiler
and staged selector supply all typing, dictionary and cache authority. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMethodScoped
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedClosureSupport
/-! Actual cached Source graphs identify the two factory lambda bodies. Their
retained ordinary provenance supplies method-aware roots and the complete
dictionary; genuine selected method bodies contain only a read and return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodScoped
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
        CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
        CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody)
      else true)) = true

def observeClosureSources (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (PLift (ObservedClosureSources fixture observed)) := do
  if checked : fixture.recipe.compiled.indexed.base.functions.all (fun named =>
    (CallableIndexedNamedGeneration.source named).nodes.all (fun node =>
      if lambdaNode node then decide (
        CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
        CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody)
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
    CallableIndexedNamedGeneration.source named = observed.makeWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeBoolRow.row.function.typedBody := by
  have row := List.all_eq_true.mp sources.checked named (List.mem_of_getElem? selected)
  have expression := List.all_eq_true.mp row (.expression node) found.1
  simpa only [lambdaNode, form, Bool.true_eq, ↓reduceIte, decide_eq_true_eq] using expression

private theorem factory_lambda_shape {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = type ∧ body = shape.body := by
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopSecondRead.form] at form; cases form
  · rw [shape.loopCall.form] at form; cases form
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.form] at form; cases form
  · rw [shape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

private theorem factory_packet {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
    (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
    (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
    (sameSource : function.source = row.row.function.typedBody) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Branching code
        (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      CallableIndexedOwnedPreparedStagedPhysicalBranchingClosureStaticSupport.SelectedBody (headers rows)
        code support.body.toContext (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have found := code.sourceFound
  rw [sameSource] at found
  have lambda := factory_lambda_shape shape nodes found code.sourceForm
  have branching : CallableIndexedOwnedPreparedStagedBranchingTree.Shape
      function.source true function.body := by
    rw [sameSource, lambda.2.2]
    exact shape.body_shape
  obtain ⟨finalContext, facts, typed, _complete⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
  have tree : GenericImperativeMatch.Syntax function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        function.source id (fun _ => False))
      support.body.context (.statements true function.body) function.resultType := by
    rw [sameSource, lambda.2.1, lambda.2.2] at typed ⊢
    exact shape.body_syntax nodes (sameSource ▸ support.body.unique) shape.children typed
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed support.caller.named function.source (fun _ => False) := by
    rw [sameSource]; exact shape.metadata nodes support.caller.named observed.noLocals
  obtain ⟨sidecar, _issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  apply CallableIndexedOwnedPreparedStagedOrdinaryMethodScopedSupport.of_actual
    stagePrepared code support provenance receiver fixture.source_wellFormed
    (fun _ impossible => False.elim impossible) metadata rows
    (fun _ impossible => False.elim impossible) checked _ methods signatureMember
    (by rw [sameSource]; exact row.sourceOwner) branching tree.prepared _ (.anonymous selected)
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

/-- The callback is derived from actual compiler provenance and original syntax.
Every supplied packet concerns the identical retained Code and dictionary. -/
theorem closure_support {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (sources : ObservedClosureSources fixture observed) (bodies : MethodBodies fixture)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {registry : SourceCoreRawMetadata.Registry} {keys}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : PacketFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SupportFor association.original (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet) := by
  rcases association with ⟨association, _slots⟩
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source] at found
    rcases sources.selected support.caller.selected (lookupExpression?_sound found) code.sourceForm with original | original
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.makeWordShape observed.makeWordNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
        rows stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.branching packet, supported⟩⟩
    · obtain ⟨packet, supported⟩ := factory_packet observed observed.makeBoolShape observed.makeBoolNodes
        (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
        rows stagePrepared receiver methods code support provenance (support.source.trans original)
      exact ⟨⟨.branching packet, supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    obtain ⟨shape⟩ := bodies.selected support.principal
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    obtain ⟨name, binder, read⟩ := shape.only_reads _ _ found
    have form := code.sourceForm
    rw [read] at form
    cases form

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))

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
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) extends ObservedCall session key arguments where
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

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
  firstValue : firstRead.completion.value = .word seed
  third : ObservedFunctionCall firstRead.completion.session observed.wordRow.row.key [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  thirdType : third.handle.sourceType = closureType .word
  firstSecond : first.handle ≠ second.handle
  firstThird : first.handle ≠ third.handle
  secondThird : second.handle ≠ third.handle
  secondRead : ObservedCall third.completion.session observed.useBoolRow.row.key [.function second.handle]
  secondValue : secondRead.completion.value = .bool false
  repeatedRead : ObservedCall secondRead.completion.session observed.useWordRow.row.key [.function first.handle]
  repeatedValue : repeatedRead.completion.value = .word seed
  thirdRead : ObservedCall repeatedRead.completion.session observed.useWordRow.row.key [.function third.handle]
  thirdValue : thirdRead.completion.value = .word (Core.Word.ofNatModulo 55)
  heapSizes : [first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [9,36,63,88,115,140,165,187]

def observeSequence (fixture : CompiledFixture) (program : ObservedProgram fixture) :
    IO (ObservedSequence fixture program) := do
  let first ← observePublicRun fixture program.wordRow.toObservedRow
  let second ← observeFunctionCall first.completion.session program.boolRow.row.key [.bool false, .bool true, .bool true]
  let ⟨secondType⟩ ← observed (second.handle.sourceType = closureType .bool) "second public handle type"
  let firstRead ← observeCall second.completion.session program.useWordRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← observed (firstRead.completion.value = .word seed) "first compiled indirect output"
  let third ← observeFunctionCall firstRead.completion.session program.wordRow.row.key [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  let ⟨thirdType⟩ ← observed (third.handle.sourceType = closureType .word) "third public handle type"
  let ⟨firstSecond⟩ ← observed (first.handle ≠ second.handle) "first/second handles distinct"
  let ⟨firstThird⟩ ← observed (first.handle ≠ third.handle) "first/third handles distinct"
  let ⟨secondThird⟩ ← observed (second.handle ≠ third.handle) "second/third handles distinct"
  let secondRead ← observeCall third.completion.session program.useBoolRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← observed (secondRead.completion.value = .bool false) "Bool compiled indirect output"
  let repeatedRead ← observeCall secondRead.completion.session program.useWordRow.row.key [.function first.handle]
  let ⟨repeatedValue⟩ ← observed (repeatedRead.completion.value = .word seed) "retained first compiled indirect output"
  let thirdRead ← observeCall repeatedRead.completion.session program.useWordRow.row.key [.function third.handle]
  let ⟨thirdValue⟩ ← observed (thirdRead.completion.value = .word (Core.Word.ofNatModulo 55)) "third compiled indirect output"
  let ⟨heapSizes⟩ ← observed ([first.session.heapSize, first.completion.session.heapSize, second.completion.session.heapSize,
    firstRead.completion.session.heapSize, third.completion.session.heapSize, secondRead.completion.session.heapSize,
    repeatedRead.completion.session.heapSize, thirdRead.completion.session.heapSize] = [9,36,63,88,115,140,165,187]) "exact seven-session heap sequence"
  return {first, second, secondType, firstRead, firstValue, third, thirdType, firstSecond, firstThird, secondThird, secondRead, secondValue, repeatedRead, repeatedValue, thirdRead, thirdValue, heapSizes}
end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedCommon
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedFactorySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

structure ObservedFactory (fixture : CompiledFixture) {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type) where
  owned : shape.expression.node.id.occurrence.owner = function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    function.typedBody shape.expression.node.id = .ok (shape.expression.node, reported)

private def confirm (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFactorySupport (fixture : CompiledFixture) {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type) : IO (ObservedFactory fixture shape) := do
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
    {type : TypeSystem.Ty} (shape : SelectedFactoryShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (extra : ObservedFactory fixture shape) (actual : ActualHeader fixture row.row)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {stages : Staging.Recursive.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token) :
    ∃ terminal : Terminal actual.header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ :=
    actual.terminal shape.expression.node.id shape.outerReturn shape.roots shape.outerReturnFound shape.outerReturnForm
  refine ⟨terminal, ?_⟩
  apply CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_branching terminal
    fixture.recipePrepared diagnostic receiver included fixture.source_wellFormed observed.profile
    observed.wordRow.entryMember (node := shape.expression.node) (reported := extra.reported)
  · rw [actual.source, expression]; exact shape.expression.found
  · exact shape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact shape.expression.requirements
  · exact shape.expression.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]
    exact .initialized shape.initializedFound shape.initializedForm
      (.whileLoop shape.loopFound shape.loopForm
        (.assign shape.assignmentFound shape.assignmentForm (.inl rfl) shape.targetBare
          (.assign shape.flagAssignmentFound shape.flagAssignmentForm (.inl rfl) shape.flagTargetBare .nil))
        (.returnValue [] shape.statementFound shape.statementForm))
  · intro context final bodyFacts typed
    rw [actual.source] at typed ⊢
    have unique : NodeOccurrencesUnique row.row.function.typedBody := by
      rw [← actual.source]
      exact actual.header.unique
    exact shape.body_syntax nodes unique (fun _ _ => True.intro) typed
  · exact point

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedMakeStep
/-! Actual factory calls append their freshly exported closures to the same physical history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
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
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = request.header.function.resultType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : RetainedState inventory receiver call.completion.session (entries ++ [entry]),
        SourceCall inventory request.header invocation state.heap arguments
          (.value entry.source) after.heap := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    RecursiveNamedPublicPhysicalClosureHistory.History.current_arguments
      (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
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
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType] at requested
  obtain ⟨reached, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    state.history.semantic.remember_success rfl request.started request.selected requested succeeded result
      (valueEq.symm.trans call.returned)
  have physicalRetained := state.history.after_result result retained
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, call.handle, payload, request.header.output,
      runOptions.outputValidationFuel⟩
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState inventory receiver call.completion.session (entries ++ [entry]) := {
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
  exact ⟨entry, rfl, rfl, handleType, next, request.rawD, request.function, sourceSize, request.sourceAt, sourceValue ▸ trace⟩

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedOrdinarySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport (Support)
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
    shape.statement shape.roots shape.statementFound shape.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun inst => inst = shape.call.instantiation) := by
    rw [actual.source]
    exact shape.metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual
    (directSites := fun inst => inst = shape.call.instantiation)
    terminal diagnostic receiver fixture.source_wellFormed (fun _ same => same ▸ supported) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows ?_
    checked ?_ methods
    (actualStagePrepared fixture) point⟩
  · intro inst same index signature target global
    subst inst
    exact covered index signature target global
  · rw [fixture.sameProgram]
    exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

include rows receiver methods in
theorem ActualHeader.use_support {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : UseShape row.row.function signature type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row) :
    ∃ terminal : Terminal actual.header,
      Nonempty (Support (headers := headers rows) (stages := actualRegistry) (semanticFaults := faults)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.value.node.id
    shape.body.statement shape.body.roots shape.body.statementFound
    shape.body.statementForm
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (fun _ => False) := by
    rw [actual.source]
    exact shape.policy_metadata nodes terminal.prepared.named noLocals
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨terminal, CallableIndexedOwnedPreparedStagedNamedPhysicalMixedTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (fun _ impossible => impossible.elim) metadata
    (by rw [expression, actual.source]; exact shape.syntax) rows
    (fun _ impossible => impossible.elim) checked ?_ methods
    (actualStagePrepared fixture) point⟩
  rw [fixture.sameProgram]
  exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
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

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 0 = 1 := (List.getElem_inj
        (i := 0) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 0 = 2 := (List.getElem_inj
        (i := 0) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 0 = 3 := (List.getElem_inj
        (i := 0) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 0 = 4 := (List.getElem_inj
        (i := 0) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.wordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 0 = 5 := (List.getElem_inj
        (i := 0) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.wordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 1 = 0 := (List.getElem_inj
        (i := 1) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 1 = 2 := (List.getElem_inj
        (i := 1) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 1 = 3 := (List.getElem_inj
        (i := 1) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 1 = 4 := (List.getElem_inj
        (i := 1) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.boolRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 1 = 5 := (List.getElem_inj
        (i := 1) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.boolRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_useWord_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.useWordRow.row.key) : header = useWordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 4 = 0 := (List.getElem_inj
        (i := 4) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 4 = 1 := (List.getElem_inj
        (i := 4) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 4 = 2 := (List.getElem_inj
        (i := 4) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 4 = 3 := (List.getElem_inj
        (i := 4) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, useBoolHeader.key] at headerKey
    have distinct : observed.useWordRow.index ≠ observed.useBoolRow.index := by
      intro equal
      have impossible : 4 = 5 := (List.getElem_inj
        (i := 4) (j := 5) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useWordRow.toObservedRow.keys_ne observed.useBoolRow.toObservedRow distinct) headerKey.symm)
theorem selected_useBool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] root header)
    (key : root.key = observed.useBoolRow.row.key) : header = useBoolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.wordRow.index := by
      intro equal
      have impossible : 5 = 0 := (List.getElem_inj
        (i := 5) (j := 0) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.wordRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.boolRow.index := by
      intro equal
      have impossible : 5 = 1 := (List.getElem_inj
        (i := 5) (j := 1) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.boolRow.toObservedRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeWordRow.index := by
      intro equal
      have impossible : 5 = 2 := (List.getElem_inj
        (i := 5) (j := 2) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeWordRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, makeBoolHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.makeBoolRow.index := by
      intro equal
      have impossible : 5 = 3 := (List.getElem_inj
        (i := 5) (j := 3) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.makeBoolRow distinct) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, useWordHeader.key] at headerKey
    have distinct : observed.useBoolRow.index ≠ observed.useWordRow.index := by
      intro equal
      have impossible : 5 = 4 := (List.getElem_inj
        (i := 5) (j := 4) (h₀ := by simp) (h₁ := by simp)
        observed.ordinarySlotsDistinct).mp equal
      omega
    exact False.elim ((observed.useBoolRow.toObservedRow.keys_ne observed.useWordRow.toObservedRow distinct) headerKey.symm)
  · exact same
section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (makeWordHeader : ActualHeader fixture observed.makeWordRow.row)
    (makeBoolHeader : ActualHeader fixture observed.makeBoolRow.row)
    (useWordHeader : ActualHeader fixture observed.useWordRow.row)
    (useBoolHeader : ActualHeader fixture observed.useBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_useWord_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useWordRow.row.key arguments fuel world store) : request.header = useWordHeader.header := by
  subst headers
  exact selected_useWord_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)

theorem selected_useBool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, makeWordHeader.header, makeBoolHeader.header, useWordHeader.header, useBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.useBoolRow.row.key arguments fuel world store) : request.header = useBoolHeader.header := by
  subst headers
  exact selected_useBool_root wordHeader boolHeader makeWordHeader makeBoolHeader useWordHeader useBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordShape.firstScheme, observed.wordShape.secondScheme,
    observed.wordShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word, .word, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = closureType .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.word_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.output = Core.CallableContract.functionType .unit .word := by
  have projected := actual.aligned.projection
  rw [actual.word_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .bool, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolShape.firstScheme, observed.boolShape.secondScheme,
    observed.boolShape.flagScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool, .bool, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = closureType .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

theorem ActualHeader.bool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.output = Core.CallableContract.functionType .unit .bool := by
  have projected := actual.aligned.projection
  rw [actual.bool_result_type] at projected
  simpa [closureType, SourceCoreCompatibleCatalog.Catalog.project,
    SourceCoreCompatibleCatalog.Catalog.functionType, observed.profile] using (Except.ok.inj projected).symm

theorem ActualHeader.useWord_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useWordShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useWordInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useWord_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.types = [closureType .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useWord_input_types

theorem ActualHeader.useWord_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useWordResultType

theorem ActualHeader.useWord_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useWordRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.useWord_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.useBool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [closureType .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.useBoolShape.body.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.useBoolInputScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.useBool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.types = [closureType .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.useBool_input_types

theorem ActualHeader.useBool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.function.resultType = .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.useBoolResultType

theorem ActualHeader.useBool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.useBoolRow.row) : actual.header.output = .bool := by
  have projected := actual.aligned.projection
  rw [actual.useBool_result_type] at projected
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
      [inventory.wordHeader.header, inventory.boolHeader.header, inventory.makeWordHeader.header, inventory.makeBoolHeader.header, inventory.useWordHeader.header, inventory.useBoolHeader.header] := by
  simp only [OrdinaryInventory.rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers,
    inventory.wordAligned, inventory.boolAligned, inventory.makeWordAligned, inventory.makeBoolAligned, inventory.useWordAligned, inventory.useBoolAligned]

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    [given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.useWordInput, given.useBoolInput].map (fun input => input.prepared.index) =
      [observed.wordRow.index, observed.boolRow.index, observed.makeWordRow.index, observed.makeBoolRow.index, observed.useWordRow.index, observed.useBoolRow.index] := by
  have word : given.wordInput.prepared.index = observed.wordRow.index := by
    have same : given.wordHeader.header.slot = given.wordInput.prepared.index := by
      rw [given.wordAligned]; exact given.wordPacket.aligned.slot
    exact same.symm.trans given.wordSlot
  have bool : given.boolInput.prepared.index = observed.boolRow.index := by
    have same : given.boolHeader.header.slot = given.boolInput.prepared.index := by
      rw [given.boolAligned]; exact given.boolPacket.aligned.slot
    exact same.symm.trans given.boolSlot
  have makeWord : given.makeWordInput.prepared.index = observed.makeWordRow.index := by
    have same : given.makeWordHeader.header.slot = given.makeWordInput.prepared.index := by
      rw [given.makeWordAligned]; exact given.makeWordPacket.aligned.slot
    exact same.symm.trans given.makeWordSlot
  have makeBool : given.makeBoolInput.prepared.index = observed.makeBoolRow.index := by
    have same : given.makeBoolHeader.header.slot = given.makeBoolInput.prepared.index := by
      rw [given.makeBoolAligned]; exact given.makeBoolPacket.aligned.slot
    exact same.symm.trans given.makeBoolSlot
  have useWord : given.useWordInput.prepared.index = observed.useWordRow.index := by
    have same : given.useWordHeader.header.slot = given.useWordInput.prepared.index := by
      rw [given.useWordAligned]; exact given.useWordPacket.aligned.slot
    exact same.symm.trans given.useWordSlot
  have useBool : given.useBoolInput.prepared.index = observed.useBoolRow.index := by
    have same : given.useBoolHeader.header.slot = given.useBoolInput.prepared.index := by
      rw [given.useBoolAligned]; exact given.useBoolPacket.aligned.slot
    exact same.symm.trans given.useBoolSlot
  simp only [List.map_cons, List.map_nil, word, bool, makeWord, makeBool, useWord, useBool]

theorem OrdinaryInventory.distinct {fixture observed} (given : OrdinaryInventory fixture observed) :
    ([given.wordInput, given.boolInput, given.makeWordInput, given.makeBoolInput, given.useWordInput, given.useBoolInput].map (fun input => input.prepared.index)).Nodup := by
  rw [given.indices]
  exact observed.ordinarySlotsDistinct

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedSeed
/-! The initial method-bearing public call connects its actual bootstrap and input
encoding to the Source result and the full returned physical cache. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (inventory : OrdinaryInventory fixture observed)
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.useWordInput, inventory.useBoolInput].map (fun input => input.prepared.index)).Nodup)
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
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = closureType .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState inventory receiver first.completion.session [entry],
        SourceCall inventory inventory.wordHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] inventory.wordHeader.header.function)
          ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 102400 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    exact word_simple seed (Core.Word.ofNatModulo 33) true
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    prepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.makeWordHeader inventory.makeBoolHeader inventory.useWordHeader inventory.useBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.wordHeader.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] inventory.wordHeader.header.types := by
    rw [inventory.wordHeader.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt inventory.wordHeader.header inventory.wordInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global inventory.wordPacket.header.named.specialized inventory.wordInput.prepared.available)) := by
    rw [inventory.wordAligned]
    exact inventory.wordPacket.sourceAt
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments.initial_data_arguments
      (inputs := [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.useWordInput, inventory.useBoolInput])
      (rows := inventory.rows) (distinct := distinct)
      (profile := observed.profile) (completion := receiver.completion)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (started := started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    inventory.wordHeader.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := receiver.completion)
      (functions := inventory.functions receiver) (packet := packet) (reflectsBodies := reflectsBodies)
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
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType] at requested
  obtain ⟨returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_remembered rfl started selected requested succeeded result
      (valueEq.symm.trans first.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨inventory.wordHeader.header.function.resultType, source, first.handle, payload,
      inventory.wordHeader.header.output, runOptions.outputValidationFuel⟩
  let state : RetainedState inventory receiver first.completion.session [entry] := {
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
  exact ⟨entry, inventory.wordHeader.word_result_type, rfl, state, inventory.wordInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedInitialForward
/-! Initial Source success determines sufficient execution and export budgets
at the original public checkpoint. Every sufficient output appends its actual
new closure handle and retains all installed method cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
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
    (distinct : ([inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.useWordInput, inventory.useBoolInput].map
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
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory inventory.wordHeader.header invocation ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value source) after) :
    InitialForwardAt inventory receiver first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 102400 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    exact started.simple_registry (booted.registry_at initial) (word_simple seed (Core.Word.ofNatModulo 33) true)
  obtain ⟨selectedHeader, selected⟩ := RecursiveNamedPublicRootCoverage.selection_of_recipe
    fixture.recipePrepared (List.mem_of_find?_eq_some started.selected) inventory.public_coverage
  have selectedEq : selectedHeader = inventory.wordHeader.header := by
    apply selected_word_root inventory.wordHeader inventory.boolHeader inventory.makeWordHeader inventory.makeBoolHeader inventory.useWordHeader inventory.useBoolHeader
      (root := root) (header := selectedHeader)
    · exact inventory.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      inventory.wordHeader.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] inventory.wordHeader.header.types := by
    rw [inventory.wordHeader.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry, receiver.registry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments.initial_data_arguments
      (inputs := [inventory.wordInput, inventory.boolInput, inventory.makeWordInput, inventory.makeBoolInput, inventory.useWordInput, inventory.useBoolInput])
      (rows := inventory.rows) (distinct := distinct) (completion := receiver.completion)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (started := started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := receiver.completion)
      (functions := inventory.functions receiver)
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
      finalMap finalWorld inventory.wordHeader.header.function.resultType source payload inventory.wordHeader.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
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
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [inventory.wordHeader.word_result_type] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨inventory.wordHeader.header.function.resultType, source, handle, payload, inventory.wordHeader.header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl started selected exported result
    reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry := started.returned_registry exported
  rw [startupRegistry, ← receiver.registry] at returnedRegistry
  let returned : RetainedState inventory receiver completion.session [entry] := {
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
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, inventory.wordHeader.word_result_type, rfl, functionValue, handleType, returned, rfl⟩

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedStep
/-! Actual named calls with Word or Bool results continue the same retained session and Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
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
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    RecursiveNamedPublicPhysicalClosureHistory.History.current_arguments
      (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
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
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans returned) represented
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedFactoryForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def FactoryForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (resultType : TypeSystem.Ty) (source : Dynamic.Value)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = closureType resultType ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = closureType resultType ∧
          ∃ returned : RetainedState inventory receiver completion.session (entries ++ [entry]),
            returned.heap = after

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
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal request.header)
    (preservesBodies : ∀ budget {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).Closure request.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers inventory.rows) (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        request.header (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked
          state.receiving.result.context.registry (inventory.functions receiver))
        (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) child
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics) budget)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall inventory request.header invocation state.heap arguments (.value source) after) :
    FactoryForwardAt (entries := entries) inventory receiver call resultType source after := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    RecursiveNamedPublicPhysicalClosureHistory.History.current_arguments
      (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
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
      finalMap finalWorld request.header.function.resultType source payload request.header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
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
  have selectedResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [selectedResult] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    request.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  rw [rawType] at requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨request.header.function.resultType, source, handle, payload, request.header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.next state.history.semantic
    rfl request.started request.selected exported result reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := state.history.after_result result retained
  have returnedRegistry := request.started.returned_registry exported
  rw [registry] at returnedRegistry
  let returned : RetainedState inventory receiver completion.session (entries ++ [entry]) := {
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
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rawType, rfl, functionValue, handleType, returned, rfl⟩

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedForward
/-! Independent Source success supplies sufficient native and output fuel at
the original public checkpoint. Every sufficient resume retains the full
physical cache and the same Source heap and prior history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (inventory : OrdinaryInventory fixture observed) (receiver : ObservedReceiver fixture observed)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments)
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
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    RecursiveNamedPublicPhysicalClosureHistory.History.current_arguments
      (profile := observed.profile)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (history := state.history)
      (started := request.started) (inputReceipts := inputs) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference
    inventory.rows request.header request.selected.member
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports
    request.header inventory.wordHeader.header fixture.source_wellFormed).2
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalFunctionPublicInvocationBounds.preserves_root
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (functions := inventory.functions receiver)
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

end Tests.SourceCoreMethodScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreMethodScopedSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

abbrev NamedSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (stages : Staging.Recursive.Registry)
    (faults : FunctionCalls.FaultRep)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) :=
  Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
    (headers := catalog) (stages := stages) (semanticFaults := faults) header terminal)
    ({ _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal //
      header.globals = compiled.indexed.base.globals.length })

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, makeWordInput, makeBoolInput, useWordInput, useBoolInput].map
    (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers toOrdinaryInventory.rows → Terminal header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    NamedSupport (headers toOrdinaryInventory.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (terminals header member)

/-- The six genuine ordinary rows retain their different compiler branches.
Implementation rows remain in the separate physical method inventory. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (factories : ObservedFactories fixture observed)
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
      rw [observed.wordInstantiation, observed.makeWordRow.target] at target
      have same := observed.makeWordRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.makeWordHeader.header, given.makeWord_member, given.makeWordSlot.trans same.2.symm,
        given.makeWordSignature.trans same.1.symm⟩)
  obtain ⟨boolTerminal, ⟨boolSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.boolRow.toObservedRow observed.boolShape observed.boolNodes observed.noLocals observed.bool_supported
    given.boolHeader (by
      intro index signature target global
      rw [observed.boolInstantiation, observed.makeBoolRow.target] at target
      have same := observed.makeBoolRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.makeBoolHeader.header, given.makeBool_member, given.makeBoolSlot.trans same.2.symm,
        given.makeBoolSignature.trans same.1.symm⟩)
  obtain ⟨makeWordTerminal, ⟨makeWordSupport⟩⟩ := ActualHeader.factory_support observed
    observed.makeWordRow observed.makeWordShape observed.makeWordNodes factories.word given.makeWordHeader receiver (fun _ _ represented => represented)
    (registry := completion.result.context.registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
    (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
  obtain ⟨makeBoolTerminal, ⟨makeBoolSupport⟩⟩ := ActualHeader.factory_support observed
    observed.makeBoolRow observed.makeBoolShape observed.makeBoolNodes factories.bool given.makeBoolHeader receiver (fun _ _ represented => represented)
    (registry := completion.result.context.registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
    (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
  obtain ⟨useWordTerminal, ⟨useWordSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useWordRow.toObservedRow observed.useWordShape observed.useWordNodes observed.noLocals given.useWordHeader
  obtain ⟨useBoolTerminal, ⟨useBoolSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useBoolRow.toObservedRow observed.useBoolShape observed.useBoolNodes observed.noLocals given.useBoolHeader
  let property := fun header => Σ terminal : Terminal header,
    NamedSupport (headers given.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header terminal
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨wordTerminal, .inl wordSupport⟩⟩
    · exact ⟨⟨boolTerminal, .inl boolSupport⟩⟩
    · exact ⟨⟨makeWordTerminal, .inr ⟨makeWordSupport, given.makeWordHeader.aligned.globals⟩⟩⟩
    · exact ⟨⟨makeBoolTerminal, .inr ⟨makeBoolSupport, given.makeBoolHeader.aligned.globals⟩⟩⟩
    · exact ⟨⟨useWordTerminal, .inl useWordSupport⟩⟩
    · exact ⟨⟨useBoolTerminal, .inl useBoolSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by rw [given.indices]; exact observed.ordinarySlotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
  }⟩

end Tests.SourceCoreMethodScoped
end
