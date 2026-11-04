import Solcore.Test.SourceSemantics.CoreLowering.Recursive.Index
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodySupportCompatibility
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationBodyFacts
import Solcore.SourceSemantics.CoreLowering.CallableCoercionBodyProvenance
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSteps
import Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarForward
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionResidual
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSourceOutcomes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Canonical scoped tests

Scoped closures in one public session of the canonical checked program.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev DirectCall := Tests.SourceCoreRecursiveIndex.DirectCall
abbrev IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :=
  Tests.SourceCoreRecursiveIndex.IdentityShape function signature .word
abbrev parameterType : TypeSystem.Ty := .product .word (.product .bool .bool)
abbrev closureType : TypeSystem.Ty := .function parameterType .word
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


structure RelayShape (function : CheckedFunction) (signature identity : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody identity initialRead.node.id .word .word
  finalRead : Read function.typedBody localBinder .word
  initialized : StatementNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  localOrdinary : localBinder.comptime = false
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some initial.value.node.id)
  initializedType : initialized.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def RelayShape.nodeList {function signature identity} (shape : RelayShape function signature identity) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
    .statement shape.initialized, .expression shape.finalRead.node, .statement shape.statement]

theorem RelayShape.statementTyping {function signature identity}
    (shape : RelayShape function signature identity) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) : CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.initialized.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  let returned : StatementFacts := {type:=.word, hasValue:=true, sawReturn:=true, control:=.returned}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton returned), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    let locals := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.localOwner
          scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible word
          quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.localRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.localDistinct]
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements word
      head.local_self head.local_scheme_requirements_self
    have initial := shape.initial.typed (fields ▸ identityMember) word initialRead
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have finalRead := shape.finalRead.typed shape.localScheme shape.localRequirements localWord
      localExtended.local_self localExtended.local_scheme_requirements_self
    have initialized : StatementHasType function.typedBody ⟨.word,0⟩ lexical shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initialized (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm finalRead shape.statementType))⟩

structure FactoryShape (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) where
  binder : TypedBinder
  argument : TypedBinder
  flag : TypedBinder
  stop : TypedBinder
  previous : TypedBinder
  initialRead : Read function.typedBody binder .word
  initial : DirectCall function.typedBody relay initialRead.node.id .word .word
  conditionRead : Read function.typedBody flag .bool
  argumentRead : Read function.typedBody argument .word
  updated : DirectCall function.typedBody relay argumentRead.node.id .word .word
  stopRead : Read function.typedBody stop .bool
  previousRead : Read function.typedBody previous .word
  final : DirectCall function.typedBody identity previousRead.node.id .word .word
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentOrdinary : argument.comptime = false
  argumentDistinct : argument.id ≠ binder.id
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOwner : flag.id.owner = function.typedBody.owner
  flagOrdinary : flag.comptime = false
  flagDistinct : flag.id ≠ binder.id
  flagArgument : flag.id ≠ argument.id
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOwner : stop.id.owner = function.typedBody.owner
  stopOrdinary : stop.comptime = false
  stopDistinct : stop.id ≠ binder.id
  stopArgument : stop.id ≠ argument.id
  stopFlag : stop.id ≠ flag.id
  previousScheme : previous.scheme = .mono .word
  previousRequirements : previous.schemeRequirements = []
  previousOwner : previous.id.owner = function.typedBody.owner
  previousOrdinary : previous.comptime = false
  previousDistinct : previous.id ≠ binder.id
  previousArgument : previous.id ≠ argument.id
  previousFlag : previous.id ≠ flag.id
  previousStop : previous.id ≠ stop.id
  parameterNames : [argument.name, flag.name, stop.name].Nodup
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [closureType]
  inputs : function.typedBody.inputs = [binder]
  binderOwner : binder.id.owner = function.typedBody.owner
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl previous (some initial.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal updated.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  flagAssignmentFound : function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment
  flagAssignmentForm : flagAssignment.form = .assignValue flagResolution .equal stopRead.node.id
  flagAssignmentType : flagAssignment.type = .unit
  flagTargetRoot : flagResolution.target.root = flag.id
  flagTargetType : flagResolution.target.type = .bool
  flagTargetBare : flagResolution.target.projections = []
  flagAssignmentRequirements : flagResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]
  loopType : loop.type = .unit
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some final.value.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [argument, flag, stop] .word [initialized.id, loop.id, innerReturn.id]
  expressionRaw : expression.rawType = closureType
  expressionType : expression.type = closureType
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = closureType

def FactoryShape.body {function signature identity relay} (shape : FactoryShape function signature identity relay) : List StatementId :=
  [shape.initialized.id, shape.loop.id, shape.innerReturn.id]

def FactoryShape.nodeList {function signature identity relay} (shape : FactoryShape function signature identity relay) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.initial.callee.node, .expression shape.initial.value.node,
    .statement shape.initialized, .expression shape.conditionRead.node, .expression shape.argumentRead.node,
    .expression shape.updated.callee.node, .expression shape.updated.value.node, .statement shape.assignment,
    .expression shape.stopRead.node, .statement shape.flagAssignment, .statement shape.loop,
    .expression shape.previousRead.node, .expression shape.final.callee.node, .expression shape.final.value.node,
    .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]

theorem FactoryShape.statementTyping {function signature identity relay}
    (shape : FactoryShape function signature identity relay) (signatures : ProgramSignatures)
    (identityMember : identity ∈ signatures.functions) (relayMember : relay ∈ signatures.functions) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type:=closureType, hasValue:=true, sawReturn:=true, control:=.returned}
  let ordinary : StatementFacts := {type:=.unit, hasValue:=false, sawReturn:=false, control:=.ordinary .unit}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have fields : lexical.signatures = signatures := by rw [head.context_fields.1]; rfl
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical closureType :=
      ⟨binders, .function (.product (.builtin .word) (.product (.builtin .bool) (.builtin .bool))) (.builtin .word)⟩
    let arguments := lexical.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner lexical shape.argument arguments := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible lexical .word from ⟨binders, .builtin .word⟩)
          quantified_fresh := by rw [shape.argumentScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.argumentRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.argumentDistinct]
    let flags := arguments.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
    have flagExtended : BinderExtends function.typedBody.owner arguments shape.flag flags := by
      apply BinderExtends.intro
      · exact {
          owned := shape.flagOwner
          scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible arguments .bool from ⟨binders, .builtin .bool⟩)
          quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.flagRequirements }
      · cases head
        simp [arguments, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.flagDistinct, shape.flagArgument]
    let parameters := flags.withLocal shape.stop.id shape.stop.scheme shape.stop.schemeRequirements
    have stopExtended : BinderExtends function.typedBody.owner flags shape.stop parameters := by
      apply BinderExtends.intro
      · exact {
          owned := shape.stopOwner
          scheme := shape.stopScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible flags .bool from ⟨binders, .builtin .bool⟩)
          quantified_fresh := by rw [shape.stopScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.stopRequirements }
      · cases head
        simp [arguments, flags, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.stopDistinct, shape.stopArgument, shape.stopFlag]
    let locals := parameters.withLocal shape.previous.id shape.previous.scheme shape.previous.schemeRequirements
    have previousExtended : BinderExtends function.typedBody.owner parameters shape.previous locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.previousOwner
          scheme := shape.previousScheme.symm ▸ SchemeWellFormed.monoAdmissible (show TypeAdmissible parameters .word from ⟨binders, .builtin .word⟩)
          quantified_fresh := by rw [shape.previousScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.previousRequirements }
      · cases head
        simp [arguments, flags, parameters, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.previousDistinct, shape.previousArgument, shape.previousFlag, shape.previousStop]
    have parameterWord : TypeAdmissible parameters .word := ⟨binders, .builtin .word⟩
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localBool : TypeAdmissible locals .bool := ⟨binders, .builtin .bool⟩
    have parameterFields : parameters.signatures = signatures := fields
    have localFields : locals.signatures = signatures := fields
    have initialRead := shape.initialRead.typed scheme shape.binderRequirements parameterWord
      (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_self)))
      (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_scheme_requirements_self)))
    have initial := shape.initial.typed (parameterFields ▸ relayMember) parameterWord initialRead
    have initializedTyped : StatementHasType function.typedBody ⟨.word,0⟩ parameters shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.previousScheme, TypeSystem.Scheme.mono] using initial
      · rw [shape.previousScheme]; rfl
      · rw [shape.previousScheme]; rfl
      · exact previousExtended
      · exact shape.initializedType
    have seedLookup : locals.LocalLookup shape.binder.id shape.binder.scheme :=
      .tail shape.previousDistinct (.tail shape.stopDistinct (.tail shape.flagDistinct (.tail shape.argumentDistinct head.local_self)))
    have flagLookup : locals.LocalLookup shape.flag.id shape.flag.scheme :=
      .tail shape.previousFlag (.tail shape.stopFlag flagExtended.local_self)
    have flagRequirements : locals.LocalSchemeRequirementsLookup shape.flag.id shape.flag.schemeRequirements :=
      .tail shape.previousFlag (.tail shape.stopFlag flagExtended.local_scheme_requirements_self)
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements localBool flagLookup flagRequirements
    have argumentTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements localWord
      (.tail shape.previousArgument (.tail shape.stopArgument (.tail shape.flagArgument argumentExtended.local_self)))
      (.tail shape.previousArgument (.tail shape.stopArgument (.tail shape.flagArgument argumentExtended.local_scheme_requirements_self)))
    have rhsTyped := shape.updated.typed (localFields ▸ relayMember) localWord argumentTyped
    have stopTyped := shape.stopRead.typed shape.stopScheme shape.stopRequirements localBool
      (.tail shape.previousStop stopExtended.local_self) (.tail shape.previousStop stopExtended.local_scheme_requirements_self)
    have previousTyped := shape.previousRead.typed shape.previousScheme shape.previousRequirements localWord
      previousExtended.local_self previousExtended.local_scheme_requirements_self
    have finalTyped := shape.final.typed (localFields ▸ identityMember) localWord previousTyped
    have writable : WritableLocal locals shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro seedLookup (scheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.updated.value.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word,1⟩ locals shape.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have flagWritable : WritableLocal locals shape.flagResolution.target.root .bool := by
      rw [shape.flagTargetRoot]
      exact .intro flagLookup (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible localBool)
        (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
    have flagAssignmentTyped : SourceAssignmentHasType function.typedBody locals shape.flagResolution .equal shape.stopRead.node.id :=
      .equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType) stopTyped shape.flagAssignmentRequirements
    have flagTyped : StatementHasType function.typedBody ⟨.word,1⟩ locals shape.flagAssignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm flagAssignmentTyped shape.flagAssignmentType
    have loopTyped := StatementHasType.whileLoop (control:=⟨.word,0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
      (.cons statementTyped (.singleton flagTyped)) shape.loopType
    have innerReturnTyped := StatementHasType.returnValue (control:=⟨.word,0⟩)
      (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm finalTyped shape.innerReturnType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id closureType := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simpa only [List.map_cons, List.map_nil] using shape.parameterNames)
          (.cons shape.argumentScheme argumentExtended (.cons shape.flagScheme flagExtended (.cons shape.stopScheme stopExtended (.nil _))))
          (.cons initializedTyped (.cons loopTyped (.singleton innerReturnTyped)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

def observeRelay (function : CheckedFunction) (signature identity : ProgramFunctionSignature) : IO (RelayShape function signature identity) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression readNode, .expression calleeNode, .expression initialNode, .statement initialized,
      .expression finalNode, .statement statement] := function.typedBody.nodes | throw (IO.userError "relay nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "relay local")
  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity initialRead.node.id calleeNode initialNode .word .word
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder finalNode .word
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "RelayShape parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "RelayShape inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "RelayShape returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "RelayShape inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "RelayShape binderRequirements"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "RelayShape localScheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "RelayShape localRequirements"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "RelayShape localOwner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "RelayShape localDistinct"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "RelayShape localOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "RelayShape roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "RelayShape initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initial.value.node.id)) "RelayShape initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "RelayShape initializedType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "RelayShape statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "RelayShape statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "RelayShape statementType"
  return {binder, localBinder, initialRead, initial, finalRead, initialized, statement, parameters, inputTypes, returns, inputs, binderRequirements, localScheme, localRequirements, localOwner, localDistinct, localOrdinary, roots, initializedFound, initializedForm, initializedType, statementFound, statementForm, statementType}

def observeFactory (function : CheckedFunction) (signature identity relay : ProgramFunctionSignature) : IO (FactoryShape function signature identity relay) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "factory inputs")
  let [.expression initialReadNode, .expression initialCallee, .expression initialNode, .statement initialized,
      .expression conditionNode, .expression argumentNode, .expression updateCallee, .expression updateNode,
      .statement assignment, .expression stopNode, .statement flagAssignment, .statement loop,
      .expression previousNode, .expression finalCallee, .expression finalNode, .statement innerReturn,
      .expression expression, .statement statement] := function.typedBody.nodes | throw (IO.userError "factory nodes")
  let .lambda [argument, flag, stop] _ _ := expression.form | throw (IO.userError "factory parameters")
  let .letDecl previous _ := initialized.form | throw (IO.userError "factory previous")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "factory assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "factory flag assignment")
  let initialRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder initialReadNode .word
  let initial ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay initialRead.node.id initialCallee initialNode .word .word
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let argumentRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody argument argumentNode .word
  let updated ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody relay argumentRead.node.id updateCallee updateNode .word .word
  let stopRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody stop stopNode .bool
  let previousRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody previous previousNode .word
  let final ← Tests.SourceCoreRecursiveIndex.observeDirect function.typedBody identity previousRead.node.id finalCallee finalNode .word .word
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "FactoryShape argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "FactoryShape argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "FactoryShape argumentOwner"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "FactoryShape argumentOrdinary"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "FactoryShape argumentDistinct"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "FactoryShape flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "FactoryShape flagRequirements"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "FactoryShape flagOwner"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "FactoryShape flagOrdinary"
  let ⟨flagDistinct⟩ ← observed (flag.id ≠ binder.id) "FactoryShape flagDistinct"
  let ⟨flagArgument⟩ ← observed (flag.id ≠ argument.id) "FactoryShape flagArgument"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "FactoryShape stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "FactoryShape stopRequirements"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "FactoryShape stopOwner"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "FactoryShape stopOrdinary"
  let ⟨stopDistinct⟩ ← observed (stop.id ≠ binder.id) "FactoryShape stopDistinct"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "FactoryShape stopArgument"
  let ⟨stopFlag⟩ ← observed (stop.id ≠ flag.id) "FactoryShape stopFlag"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "FactoryShape previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "FactoryShape previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "FactoryShape previousOwner"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "FactoryShape previousOrdinary"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "FactoryShape previousDistinct"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "FactoryShape previousArgument"
  let ⟨previousFlag⟩ ← observed (previous.id ≠ flag.id) "FactoryShape previousFlag"
  let ⟨previousStop⟩ ← observed (previous.id ≠ stop.id) "FactoryShape previousStop"
  let ⟨parameterNames⟩ ← observed ([argument.name, flag.name, stop.name].Nodup) "FactoryShape parameterNames"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "FactoryShape parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "FactoryShape inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [closureType]) "FactoryShape returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "FactoryShape inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "FactoryShape binderOwner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "FactoryShape binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "FactoryShape roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "FactoryShape initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initial.value.node.id)) "FactoryShape initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "FactoryShape initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "FactoryShape assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal updated.value.node.id) "FactoryShape assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "FactoryShape assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "FactoryShape targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "FactoryShape targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "FactoryShape targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "FactoryShape assignmentRequirements"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "FactoryShape flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stopRead.node.id) "FactoryShape flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "FactoryShape flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "FactoryShape flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "FactoryShape flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "FactoryShape flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "FactoryShape flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "FactoryShape loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "FactoryShape loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "FactoryShape loopType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "FactoryShape innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some final.value.node.id)) "FactoryShape innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "FactoryShape innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "FactoryShape expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "FactoryShape statementFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [argument, flag, stop] .word [initialized.id, loop.id, innerReturn.id]) "FactoryShape lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = closureType) "FactoryShape expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = closureType) "FactoryShape expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "FactoryShape requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "FactoryShape coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "FactoryShape returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = closureType) "FactoryShape statementType"
  return {binder, argument, flag, stop, previous, initialRead, initial, conditionRead, argumentRead, updated, stopRead, previousRead, final, initialized, assignment, resolution, flagAssignment, flagResolution, loop, innerReturn, expression, statement, argumentScheme, argumentRequirements, argumentOwner, argumentOrdinary, argumentDistinct, flagScheme, flagRequirements, flagOwner, flagOrdinary, flagDistinct, flagArgument, stopScheme, stopRequirements, stopOwner, stopOrdinary, stopDistinct, stopArgument, stopFlag, previousScheme, previousRequirements, previousOwner, previousOrdinary, previousDistinct, previousArgument, previousFlag, previousStop, parameterNames, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, statementFound, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function identity(value: Word) returns (Word) { return value; } function relay(value: Word) returns (Word) { let local: Word = identity(value); return local; } function make(seed: Word) returns (function(Word, Bool, Bool) returns (Word)) { return lam(next: Word, flag: Bool, stop: Bool) { let previous: Word = relay(seed); while (flag) { seed = relay(next); flag = stop; } return identity(previous); }; }"}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  identityFunction : CheckedFunction
  identitySignature : ProgramFunctionSignature
  relayFunction : CheckedFunction
  relaySignature : ProgramFunctionSignature
  makeFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  functions : program.functions = [identityFunction, relayFunction, makeFunction]
  signatures : program.signatures.functions = [identitySignature, relaySignature, makeSignature]
  methods : program.methods = []
  identityDeclaration : identityFunction.declaration = identitySignature.id
  relayDeclaration : relayFunction.declaration = relaySignature.id
  makeDeclaration : makeFunction.declaration = makeSignature.id
  identityRelay : identitySignature.id ≠ relaySignature.id
  identityMake : identitySignature.id ≠ makeSignature.id
  relayMake : relaySignature.id ≠ makeSignature.id
  identityShape : IdentityShape identityFunction identitySignature
  relayShape : RelayShape relayFunction relaySignature identitySignature
  makeShape : FactoryShape makeFunction makeSignature identitySignature relaySignature
  identityNodes : identityFunction.typedBody.nodes = identityShape.nodeList
  relayNodes : relayFunction.typedBody.nodes = relayShape.nodeList
  makeNodes : makeFunction.typedBody.nodes = makeShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [identityFunction, relayFunction, makeFunction], [identitySignature, relaySignature, makeSignature] =>
      let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityFunction identitySignature .word
      let relayShape ← observeRelay relayFunction relaySignature identitySignature
      let makeShape ← observeFactory makeFunction makeSignature identitySignature relaySignature
      let ⟨methods⟩ ← observed (program.methods = []) "scoped methods"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨relayDeclaration⟩ ← observed (relayFunction.declaration = relaySignature.id) "relay declaration"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨identityRelay⟩ ← observed (identitySignature.id ≠ relaySignature.id) "identityRelay"
      let ⟨identityMake⟩ ← observed (identitySignature.id ≠ makeSignature.id) "identityMake"
      let ⟨relayMake⟩ ← observed (relaySignature.id ≠ makeSignature.id) "relayMake"
      let ⟨identityNodes⟩ ← observed (identityFunction.typedBody.nodes = identityShape.nodeList) "identity nodes"
      let ⟨relayNodes⟩ ← observed (relayFunction.typedBody.nodes = relayShape.nodeList) "relay nodes"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = makeShape.nodeList) "make nodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact identityShape.statementTyping program.signatures (fun _ binders => ⟨binders, .builtin .word⟩)
          · exact False.elim (identityRelay (identityDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identityDeclaration.symm.trans identity))
          · exact False.elim (identityRelay (identity.symm.trans relayDeclaration))
          · exact relayShape.statementTyping program.signatures (by simp [signatures])
          · exact False.elim (relayMake (relayDeclaration.symm.trans identity))
          · exact False.elim (identityMake (identity.symm.trans makeDeclaration))
          · exact False.elim (relayMake (identity.symm.trans makeDeclaration))
          · exact makeShape.statementTyping program.signatures (by simp [signatures]) (by simp [signatures])
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {
        program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep
        identityFunction, relayFunction, makeFunction, identitySignature, relaySignature, makeSignature, functions, signatures, methods, identityDeclaration, relayDeclaration, makeDeclaration, identityRelay, identityMake, relayMake, identityShape, relayShape, makeShape, identityNodes, relayNodes, makeNodes }
    | _, _ => throw (IO.userError "scoped declaration count")

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
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
  let seeds := [SourceCompiler.Seed.declaration checked.identitySignature.id,
    SourceCompiler.Seed.declaration checked.makeSignature.id, SourceCompiler.Seed.declaration checked.relaySignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
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
    (CoreLowering.CallableNamedMetadata.instantiation row) header
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
    instantiation := CallableNamedMetadata.instantiation row
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
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  assumptions : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨assumptions⟩ ← observed (row.assumptions = []) "direct row assumptions"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          assumptions := assumptions
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
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

def RelayDirectSites (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ id node, source.lookupExpression? id = some node → ∀ callee ids instantiation,
    node.form = .call callee ids (.declaration instantiation) →
    CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows instantiation

private def relayDirectNode (rows : List SourceSpecialization.SpecializedFunction) : Node → Prop
  | .expression expression => match expression.form with
    | .call _ _ (.declaration instantiation) =>
        CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite rows instantiation
    | _ => True
  | .statement _ => True

private def relayDirectNode? (rows : List SourceSpecialization.SpecializedFunction)
    (node : Node) : Option (PLift (relayDirectNode rows node)) :=
  match node with
  | .statement _ => some ⟨True.intro⟩
  | .expression expression => by
      cases form : expression.form
      case call callee ids resolution =>
        cases resolution
        case declaration instantiation =>
          exact do
            let ⟨site⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation
            pure ⟨by simpa only [relayDirectNode, form] using site⟩
        all_goals exact some ⟨by simp only [relayDirectNode, form]⟩
      all_goals exact some ⟨by simp only [relayDirectNode, form]⟩

private def relayAll? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← relayAll? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

/-- This finite check authenticates declaration metadata in every stored node.
It does not traverse expressions or construct expression syntax. -/
def relayDirectSites? (source : TypedSource) (rows : List SourceSpecialization.SpecializedFunction) :
    Option (PLift (RelayDirectSites source rows)) := do
  let ⟨all⟩ ← relayAll? (relayDirectNode rows) (relayDirectNode? rows) source.nodes
  pure ⟨by
    intro id node found callee ids instantiation form
    have selected := all (.expression node) (lookupExpression?_sound found).1
    simpa only [relayDirectNode, form] using selected⟩

/-- Only the actual cache, expression metadata and direct targets are checked.
The accepted compiler action later supplies statement and expression structure. -/
structure ObservedRelayAdmission (fixture : CompiledFixture)
    (row : ObservedRow fixture fixture.relaySignature) where
  named : SourceCoreGeneralFunctions.Function
  selected : fixture.recipe.compiled.indexed.base.functions[row.index]? = some named
  same : named.specialized = row.row
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table fixture.recipe.compiled
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    fixture.recipe.compiled.indexed named named.specialized.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite table.rows)
  metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    fixture.recipe.compiled.indexed named named.specialized.function.typedBody
    (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite table.rows) = some ⟨metadata⟩
  requirements : CallableIndexedOwnedPreparedNamedEvidenceAdmission.Requirements named.specialized.function.typedBody
  requirementsAccepted : CallableIndexedOwnedPreparedNamedEvidenceAdmission.requirements?
    named.specialized.function.typedBody = some ⟨requirements⟩
  sites : RelayDirectSites named.specialized.function.typedBody table.rows
  sitesAccepted : relayDirectSites? named.specialized.function.typedBody table.rows = some ⟨sites⟩

def observeRelayAdmission (fixture : CompiledFixture)
    (row : ObservedRow fixture fixture.relaySignature) : IO (ObservedRelayAdmission fixture row) := do
  match selected : fixture.recipe.compiled.indexed.base.functions[row.index]? with
  | none => throw (IO.userError "actual relay cache row missing")
  | some named =>
    let ⟨sameRaw⟩ ← observed ((named.specialized == row.row) = true) "actual relay full cache metadata"
    have same : named.specialized = row.row := eq_of_beq sameRaw
    let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect fixture.recipe.compiled
      fixture.source_wellFormed 100
    match metadataAccepted : CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
        fixture.recipe.compiled.indexed named named.specialized.function.typedBody
        (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite table.rows) with
    | none => throw (IO.userError "actual relay expression metadata rejected")
    | some metadata =>
      match requirementsAccepted : CallableIndexedOwnedPreparedNamedEvidenceAdmission.requirements?
          named.specialized.function.typedBody with
      | none => throw (IO.userError "actual relay evidence requirements rejected")
      | some requirements =>
        match sitesAccepted : relayDirectSites? named.specialized.function.typedBody table.rows with
        | none => throw (IO.userError "actual relay direct target rejected")
        | some sites => pure ⟨named, selected, same, table, metadata.down, metadataAccepted,
            requirements.down, requirementsAccepted, sites.down, sitesAccepted⟩

structure ObservedProgram (fixture : CompiledFixture) where
  identityRow : ObservedRow fixture fixture.identitySignature
  makeRow : ObservedRow fixture fixture.makeSignature
  relayRow : ObservedRow fixture fixture.relaySignature
  relayAdmission : ObservedRelayAdmission fixture relayRow
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 3
  identityMake : identityRow.index ≠ makeRow.index
  identityRelay : identityRow.index ≠ relayRow.index
  makeRelay : makeRow.index ≠ relayRow.index
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature fixture.identitySignature fixture.relaySignature
  relayShape : RelayShape relayRow.row.function fixture.relaySignature fixture.identitySignature
  identityNodes : identityRow.row.function.typedBody.nodes = identityShape.nodeList
  makeNodes : makeRow.row.function.typedBody.nodes = makeShape.nodeList
  relayNodes : relayRow.row.function.typedBody.nodes = relayShape.nodeList
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let identityRow ← observeRow fixture fixture.identitySignature
  let makeRow ← observeRow fixture fixture.makeSignature
  let relayRow ← observeRow fixture fixture.relaySignature
  let relayAdmission ← observeRelayAdmission fixture relayRow
  let identityShape ← Tests.SourceCoreRecursiveIndex.observeIdentity identityRow.row.function fixture.identitySignature .word
  let makeShape ← observeFactory makeRow.row.function fixture.makeSignature fixture.identitySignature fixture.relaySignature
  let relayShape ← observeRelay relayRow.row.function fixture.relaySignature fixture.identitySignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 3) "direct compiled globalsLength"
  let ⟨identityMake⟩ ← observed (identityRow.index ≠ makeRow.index) "direct compiled identityMake"
  let ⟨identityRelay⟩ ← observed (identityRow.index ≠ relayRow.index) "direct compiled identityRelay"
  let ⟨makeRelay⟩ ← observed (makeRow.index ≠ relayRow.index) "direct compiled makeRelay"
  let ⟨identityNodes⟩ ← observed (identityRow.row.function.typedBody.nodes = identityShape.nodeList) "direct compiled identityNodes"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = makeShape.nodeList) "direct compiled makeNodes"
  let ⟨relayNodes⟩ ← observed (relayRow.row.function.typedBody.nodes = relayShape.nodeList) "direct compiled relayNodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "direct compiled noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "direct compiled profile"
  return {identityRow, makeRow, relayRow, relayAdmission, identityShape, makeShape, relayShape, globalsLength, identityMake, identityRelay, makeRelay, identityNodes, makeNodes, relayNodes, noLocals, profile}

/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
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

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- All three real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (identityInput makeInput relayInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      identityInput.row = observed.identityRow.row ∧ makeInput.row = observed.makeRow.row ∧ relayInput.row = observed.relayRow.row ∧
      ∃ (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput)
        (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (relayPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayInput),
      ∃ (identityHeader : ActualHeader fixture observed.identityRow.row)
        (makeHeader : ActualHeader fixture observed.makeRow.row)
        (relayHeader : ActualHeader fixture observed.relayRow.row),
        identityHeader.header = identityPacket.header ∧ makeHeader.header = makePacket.header ∧ relayHeader.header = relayPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers
            (.cons identityPacket (.cons makePacket (.cons relayPacket .nil)))) := by
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨relayInput, relayRow, relayPacket, relayHeader, relayEq, relaySlot, relaySignature⟩ := observed.relayRow.issue
  refine ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, ?_⟩
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .head _
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .tail _ (.head _)
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨relayHeader.header, ?_, relaySlot.trans same.symm, ?_⟩
    · rw [relayEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.relayRow.slot.selected] at found
      exact relaySignature.trans (Option.some.inj found)

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

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
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
        match returned : completion.value with
        | .function handle =>
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")


theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.identityRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.identityNodes, Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [observed.identityShape.read.form] at form; cases form
  · cases same

theorem ObservedProgram.relay_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.relayRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.relayNodes, RelayShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same | same
  all_goals try cases same
  · rw [observed.relayShape.initialRead.form] at form; cases form
  · rw [observed.relayShape.initial.calleeForm] at form; cases form
  · rw [observed.relayShape.initial.form] at form; cases form
  · rw [observed.relayShape.finalRead.form] at form; cases form

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

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedIdentitySupport
/-! The actual identity row is a compiler-produced read body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem identity_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.identityRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.identityShape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.identityNodes] at present
  simpa only [Tests.SourceCoreRecursiveIndex.IdentityShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ActualHeader.identity_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [identity_expression observed found]
    exact observed.identityShape.read.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [identity_expression observed found, observed.identityShape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.identityShape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read observed.identityShape.read.found observed.identityShape.read.form)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.identity_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.identityShape.read.node.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.identity_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.identity_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.identity_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.identityRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.identityShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.identityShape.read.node.id
    observed.identityShape.statement observed.identityShape.roots observed.identityShape.statementFound observed.identityShape.statementForm
  exact ⟨terminal, expression, ActualHeader.identity_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedRuntime
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics

def secondSeed : Core.Word := Core.Word.ofNatModulo 20
def interveningSeed : Core.Word := Core.Word.ofNatModulo 30

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

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle argument runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle argument runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "direct issued call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "direct issued call exhausted")
  | .ok (.succeeded completion) => pure ⟨completion, result ▸ executed.property⟩


def firstNext : Core.Word := Core.Word.ofNatModulo 11
def secondNext : Core.Word := Core.Word.ofNatModulo 21
def repeatedNext : Core.Word := Core.Word.ofNatModulo 12

def packed (next : Core.Word) (flag stop : Bool) : SourceCorePublicValues.Value :=
  .product (.word next) (.product (.bool flag) (.bool stop))

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  firstRead : ObservedInvocation second.completion.session first.handle (packed firstNext true false)
  firstValue : firstRead.completion.value = .word seed
  intervening : ObservedFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
  secondRead : ObservedInvocation intervening.completion.session second.handle (packed secondNext true false)
  secondValue : secondRead.completion.value = .word secondSeed
  repeatedRead : ObservedInvocation secondRead.completion.session first.handle (packed repeatedNext false false)
  repeatedValue : repeatedRead.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  if distinct : first.handle ≠ second.handle then
    let firstRead ← observeInvocation second.completion.session first.handle (packed firstNext true false)
    if firstValue : firstRead.completion.value = .word seed then
      let intervening ← observeFunctionCall firstRead.completion.session observed.makeRow.row.key [.word interveningSeed]
      let secondRead ← observeInvocation intervening.completion.session second.handle (packed secondNext true false)
      if secondValue : secondRead.completion.value = .word secondSeed then
        let repeatedRead ← observeInvocation secondRead.completion.session first.handle (packed repeatedNext false false)
        if repeatedValue : repeatedRead.completion.value = .word seed then
          return {first, second, distinct, firstRead, firstValue, intervening, secondRead, secondValue, repeatedRead, repeatedValue}
        else throw (IO.userError "scoped direct captured mutation reached the next call")
      else throw (IO.userError "closure direct second capture not20")
    else throw (IO.userError "closure direct first capture not10")
  else throw (IO.userError "closure direct lost distinct captures")

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

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
    {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (expression : ExpressionNode) (expressionFound : source.lookupExpression? expression.id = some expression) (expressionType : expression.type = .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression.id))
    (annotation : node.type = .word) (leaf : approved expression.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation expressionFound expressionType
        (by simpa only [expressionType] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (expression : ExpressionNode) (expressionFound : source.lookupExpression? expression.id = some expression) (expressionType : expression.type = payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal expression.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved expression.id)
    (typed : SourceAssignmentHasType source context assignment .equal expression.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
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
    {binder : TypedBinder} {node : StatementNode} {expression : ExpressionNode}
    {approved : ExpressionId → Prop} {rest : List StatementId}
    (found : source.lookupStatement? node.id = some node)
    (form : node.form = .letDecl binder (some expression.id))
    (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
    (scheme : binder.scheme = .mono .word)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = .word) (leaf : approved expression.id)
    (typed : Dynamic.StatementHasType.FormTyping source {returnType := .word} context node.form middle)
    (remaining : GenericImperativeMatch.Syntax source approved middle (.statements true rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements true (node.id :: rest)) .word := by
  rw [form] at typed
  cases typed with
  | letInitialized value mono extended =>
    exact .initialized found form declaration mono extended ordinary expressionFound
      (by rw [expressionType, scheme]; rfl)
      (by simpa only [scheme, TypeSystem.Scheme.mono, expressionType] using value) leaf remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [scheme]; rfl))

theorem ObservedProgram.make_seed_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (seedScheme : observed.makeShape.binder.scheme = .mono .word) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.binder.id = .ok observed.makeShape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.binderOwner, observed.makeShape.argumentDistinct, observed.makeShape.flagDistinct, observed.makeShape.stopDistinct, observed.makeShape.previousDistinct, seedScheme, observed.makeShape.binderRequirements]

theorem ObservedProgram.make_flag_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.flag.id = .ok observed.makeShape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.flagOwner, Ne.symm observed.makeShape.flagDistinct, Ne.symm observed.makeShape.flagArgument, observed.makeShape.stopFlag, observed.makeShape.previousFlag, observed.makeShape.flagScheme, observed.makeShape.flagRequirements]

theorem ObservedProgram.make_previous_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.previous.id = .ok observed.makeShape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.previousOwner, Ne.symm observed.makeShape.previousDistinct, Ne.symm observed.makeShape.previousArgument, Ne.symm observed.makeShape.previousFlag, Ne.symm observed.makeShape.previousStop, observed.makeShape.previousScheme, observed.makeShape.previousRequirements]

theorem ObservedProgram.relay_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.relayRow.row.function.typedBody observed.relayShape.localBinder.id = .ok observed.relayShape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.relayShape.inputs,
    observed.relayNodes, RelayShape.nodeList, observed.relayShape.initialRead.form,
    observed.relayShape.initial.calleeForm, observed.relayShape.initial.form,
    observed.relayShape.finalRead.form, observed.relayShape.initializedForm, observed.relayShape.statementForm,
    observed.relayShape.localOwner, Ne.symm observed.relayShape.localDistinct,
    observed.relayShape.localScheme, TypeSystem.Scheme.mono, observed.relayShape.localRequirements]

theorem ObservedProgram.make_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.makeRow.row.function.typedBody true observed.makeShape.body :=
  .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
    (.whileLoop observed.makeShape.loopFound observed.makeShape.loopForm
      (.assign observed.makeShape.assignmentFound observed.makeShape.assignmentForm (.inl rfl) observed.makeShape.targetBare
        (.assign observed.makeShape.flagAssignmentFound observed.makeShape.flagAssignmentForm (.inl rfl) observed.makeShape.flagTargetBare .nil))
      (.returnValue [] observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm))

def ObservedProgram.childIds {fixture : CompiledFixture} (observed : ObservedProgram fixture) : List ExpressionId :=
  [observed.makeShape.initial.value.node.id, observed.makeShape.conditionRead.node.id,
    observed.makeShape.updated.value.node.id, observed.makeShape.stopRead.node.id, observed.makeShape.final.value.node.id]

theorem ObservedProgram.make_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (seedScheme : observed.makeShape.binder.scheme = .mono .word)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.makeRow.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.childIds, approved id)
    (typed : StatementsHaveType observed.makeRow.row.function.typedBody {returnType := .word}
      context observed.makeShape.body final facts) :
    GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved context
      (.statements true observed.makeShape.body) .word := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax observed.makeShape.initializedFound observed.makeShape.initializedForm
    observed.make_previous_declaration observed.makeShape.previousScheme
    (by simp [observed.makeShape.inputs, Ne.symm observed.makeShape.previousDistinct])
    observed.makeShape.initial.value.found observed.makeShape.initial.value.type
    (leaves _ (by simp [childIds])) (form_at unique observed.makeShape.initializedFound initialized)
  obtain ⟨middle, _, _, first, suffix⟩ := head_tail tail
  have firstForm := form_at unique observed.makeShape.loopFound first
  rw [observed.makeShape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop observed.makeShape.loopFound observed.makeShape.loopForm
      observed.makeShape.conditionRead.found observed.makeShape.conditionRead.type
      (by simpa only [observed.makeShape.conditionRead.type] using conditionTyped) (leaves _ (by simp [childIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.makeShape.assignmentFound assignedHead
      rw [observed.makeShape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned observed.makeShape.updated.value.node observed.makeShape.updated.value.found observed.makeShape.updated.value.type
          observed.makeShape.assignmentFound observed.makeShape.assignmentForm
          (by rw [observed.makeShape.targetRoot]; exact observed.make_seed_declaration seedScheme)
          seedScheme observed.makeShape.targetBare observed.makeShape.targetType
          (leaves _ (by simp [childIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique observed.makeShape.flagAssignmentFound flagHead
        rw [observed.makeShape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned observed.makeShape.stopRead.node observed.makeShape.stopRead.found observed.makeShape.stopRead.type
            observed.makeShape.flagAssignmentFound observed.makeShape.flagAssignmentForm
            (by rw [observed.makeShape.flagTargetRoot]; exact observed.make_flag_declaration)
            observed.makeShape.flagScheme observed.makeShape.flagTargetBare observed.makeShape.flagTargetType
            (leaves _ (by simp [childIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail suffix
      exact returning unique observed.makeShape.final.value.node observed.makeShape.final.value.found
        observed.makeShape.final.value.type observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm
        observed.makeShape.innerReturnType (leaves _ (by simp [childIds])) returningHead

theorem ObservedProgram.relay_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.relayRow.row.function.typedBody true
      [observed.relayShape.initialized.id, observed.relayShape.statement.id] :=
  .initialized observed.relayShape.initializedFound observed.relayShape.initializedForm
    (.returnValue [] observed.relayShape.statementFound observed.relayShape.statementForm)

theorem ObservedProgram.relay_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.relayRow.row.function.typedBody) {approved : ExpressionId → Prop}
    (initialApproved : approved observed.relayShape.initial.value.node.id)
    (finalApproved : approved observed.relayShape.finalRead.node.id)
    (typed : StatementsHaveType observed.relayRow.row.function.typedBody {returnType := .word}
      context [observed.relayShape.initialized.id, observed.relayShape.statement.id] final facts) :
    GenericImperativeMatch.Syntax observed.relayRow.row.function.typedBody approved context
      (.statements true [observed.relayShape.initialized.id, observed.relayShape.statement.id]) .word := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax observed.relayShape.initializedFound observed.relayShape.initializedForm
    observed.relay_local_declaration observed.relayShape.localScheme
    (by simp [observed.relayShape.inputs, Ne.symm observed.relayShape.localDistinct])
    observed.relayShape.initial.value.found observed.relayShape.initial.value.type initialApproved
    (form_at unique observed.relayShape.initializedFound initialized)
  obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
  exact returning unique observed.relayShape.finalRead.node observed.relayShape.finalRead.found
    observed.relayShape.finalRead.type observed.relayShape.statementFound observed.relayShape.statementForm
    observed.relayShape.statementType finalApproved returningHead

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ObservedProgram.make_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.makeShape.initialRead.node ∨ node = observed.makeShape.initial.callee.node ∨ node = observed.makeShape.initial.value.node ∨ node = observed.makeShape.conditionRead.node ∨ node = observed.makeShape.argumentRead.node ∨ node = observed.makeShape.updated.callee.node ∨ node = observed.makeShape.updated.value.node ∨ node = observed.makeShape.stopRead.node ∨ node = observed.makeShape.previousRead.node ∨ node = observed.makeShape.final.callee.node ∨ node = observed.makeShape.final.value.node ∨ node = observed.makeShape.expression := by
  have present := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at present
  simpa only [FactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.make_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.makeRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.requirements
    · exact observed.makeShape.initial.callee.requirements
    · exact observed.makeShape.initial.value.requirements
    · exact observed.makeShape.conditionRead.requirements
    · exact observed.makeShape.argumentRead.requirements
    · exact observed.makeShape.updated.callee.requirements
    · exact observed.makeShape.updated.value.requirements
    · exact observed.makeShape.stopRead.requirements
    · exact observed.makeShape.previousRead.requirements
    · exact observed.makeShape.final.callee.requirements
    · exact observed.makeShape.final.value.requirements
    · exact observed.makeShape.requirements
  · intro id _ node found
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact observed.makeShape.initialRead.coercions
    · exact observed.makeShape.initial.callee.coercions
    · exact observed.makeShape.initial.value.coercions
    · exact observed.makeShape.conditionRead.coercions
    · exact observed.makeShape.argumentRead.coercions
    · exact observed.makeShape.updated.callee.coercions
    · exact observed.makeShape.updated.value.coercions
    · exact observed.makeShape.stopRead.coercions
    · exact observed.makeShape.previousRead.coercions
    · exact observed.makeShape.final.callee.coercions
    · exact observed.makeShape.final.value.coercions
    · exact observed.makeShape.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst node
    · rw [observed.makeShape.initialRead.form] at form; cases form
    · rw [observed.makeShape.initial.calleeForm] at form; cases form
    · rw [observed.makeShape.initial.form] at form; cases form
    · rw [observed.makeShape.conditionRead.form] at form; cases form
    · rw [observed.makeShape.argumentRead.form] at form; cases form
    · rw [observed.makeShape.updated.calleeForm] at form; cases form
    · rw [observed.makeShape.updated.form] at form; cases form
    · rw [observed.makeShape.stopRead.form] at form; cases form
    · rw [observed.makeShape.previousRead.form] at form; cases form
    · rw [observed.makeShape.final.calleeForm] at form; cases form
    · rw [observed.makeShape.final.form] at form; cases form
    · rw [observed.makeShape.lambda] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem ObservedProgram.relay_expressions {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.relayRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.relayShape.initialRead.node ∨ node = observed.relayShape.initial.callee.node ∨ node = observed.relayShape.initial.value.node ∨ node = observed.relayShape.finalRead.node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.relayNodes] at present
  simpa only [RelayShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

theorem ObservedProgram.relay_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (named : CallableIndexedNamedGeneration.Named)
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.relayRow.row.function.typedBody := by
  constructor
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · exact observed.relayShape.initialRead.requirements
    · exact observed.relayShape.initial.callee.requirements
    · exact observed.relayShape.initial.value.requirements
    · exact observed.relayShape.finalRead.requirements
  · intro id _ node found
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · exact observed.relayShape.initialRead.coercions
    · exact observed.relayShape.initial.callee.coercions
    · exact observed.relayShape.initial.value.coercions
    · exact observed.relayShape.finalRead.coercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases observed.relay_expressions found with same | same | same | same
    all_goals subst node
    · rw [observed.relayShape.initialRead.form] at form; cases form
    · rw [observed.relayShape.initial.calleeForm] at form; cases form
    · rw [observed.relayShape.initial.form] at form; cases form
    · rw [observed.relayShape.finalRead.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [observed.noLocals, List.any_nil]

theorem DirectCall.syntax {source : TypedSource} {signature : ProgramFunctionSignature}
    {argument : ExpressionId} {parameter result : TypeSystem.Ty}
    (call : DirectCall source signature argument parameter result)
    (child : GeneralSyntax source argument) : GeneralSyntax source call.value.node.id := by
  refine .direct call.value.found call.form ?_ ?_
  · rw [call.exact]; exact ⟨rfl, rfl⟩
  · intro id member
    cases List.mem_singleton.mp member
    exact child

theorem ObservedProgram.make_children {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∀ id ∈ observed.childIds, GeneralSyntax observed.makeRow.row.function.typedBody id := by
  intro id member
  simp only [childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact observed.makeShape.initial.syntax (.leaf (.read observed.makeShape.initialRead.found observed.makeShape.initialRead.form))
  · exact .leaf (.read observed.makeShape.conditionRead.found observed.makeShape.conditionRead.form)
  · exact observed.makeShape.updated.syntax (.leaf (.read observed.makeShape.argumentRead.found observed.makeShape.argumentRead.form))
  · exact .leaf (.read observed.makeShape.stopRead.found observed.makeShape.stopRead.form)
  · exact observed.makeShape.final.syntax (.leaf (.read observed.makeShape.previousRead.found observed.makeShape.previousRead.form))

theorem ObservedProgram.relay_initial_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    GeneralSyntax observed.relayRow.row.function.typedBody observed.relayShape.initial.value.node.id :=
  observed.relayShape.initial.syntax (.leaf (.read observed.relayShape.initialRead.found observed.relayShape.initialRead.form))

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedMakeSupport
/-! Concrete make support and the complete closure family for the three-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedCallFaults.faults
      completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic receiver included fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]
    exact .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
      (.whileLoop observed.makeShape.loopFound observed.makeShape.loopForm
        (.assign observed.makeShape.assignmentFound observed.makeShape.assignmentForm (.inl rfl) observed.makeShape.targetBare
          (.assign observed.makeShape.flagAssignmentFound observed.makeShape.flagAssignmentForm (.inl rfl) observed.makeShape.flagTargetBare .nil))
        (.returnValue [] observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm))
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact observed.make_body_syntax extra.binderScheme (actual.source ▸ actual.header.unique)
      (fun _ _ => True.intro) typed


theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedCallFaults.faults
      completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression receiver included
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.relayRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) relayHeader.prepared.same

theorem ObservedProgram.cached_rows {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized = observed.identityRow.row ∨
    named.specialized = observed.makeRow.row ∨
    named.specialized = observed.relayRow.row := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 3 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have relayBound := (List.getElem?_eq_some_iff.mp observed.relayRow.slot.selected).1
  rw [observed.globalsLength] at identityBound makeBound relayBound
  have casesIndex : index = observed.identityRow.index ∨ index = observed.makeRow.index ∨ index = observed.relayRow.index := by
    have im := observed.identityMake
    have ir := observed.identityRelay
    have mr := observed.makeRelay
    omega
  rcases casesIndex with same | same | same
  · left
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact identityHeader.prepared.same
  · right; left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact makeHeader.prepared.same
  · right; right
    have actualIndex := (observed.relayRow.prepared_slot relayHeader.prepared).2
    rw [same, ← actualIndex, relayHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact relayHeader.prepared.same

theorem ObservedProgram.cached_assumptions {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    named.specialized.assumptions = [] := by
  rcases observed.cached_rows identityHeader makeHeader relayHeader selected with same | same | same
  · rw [same]; exact observed.identityRow.assumptions
  · rw [same]; exact observed.makeRow.assumptions
  · rw [same]; exact observed.relayRow.assumptions

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [observed.makeShape.argument, observed.makeShape.flag, observed.makeShape.stop] ∧
      result = .word ∧ body = observed.makeShape.body := by
  rcases observed.make_expressions found with same | same | same | same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [observed.makeShape.initialRead.form] at form; cases form
  · rw [observed.makeShape.initial.calleeForm] at form; cases form
  · rw [observed.makeShape.initial.form] at form; cases form
  · rw [observed.makeShape.conditionRead.form] at form; cases form
  · rw [observed.makeShape.argumentRead.form] at form; cases form
  · rw [observed.makeShape.updated.calleeForm] at form; cases form
  · rw [observed.makeShape.updated.form] at form; cases form
  · rw [observed.makeShape.stopRead.form] at form; cases form
  · rw [observed.makeShape.previousRead.form] at form; cases form
  · rw [observed.makeShape.final.calleeForm] at form; cases form
  · rw [observed.makeShape.final.form] at form; cases form
  · rw [observed.makeShape.lambda] at form
    obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
    exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    (extra : ObservedMake fixture observed)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader relayHeader support.caller.selected with original | original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.relay_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    have resultShape := (observed.make_lambda_shape found code.sourceForm).2.1
    have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
      rw [sameSource, bodyShape]; exact observed.make_body_shape
    obtain ⟨_final, _facts, bodyTyped, _completes⟩ := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
      support.body.frame support.body.extended
    have tree : GenericImperativeMatch.Syntax function.source
        (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax function.source)
        support.body.context (.statements true function.body) function.resultType := by
      rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
      exact observed.make_body_syntax extra.binderScheme (sameSource ▸ support.body.unique) observed.make_children bodyTyped
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader relayHeader support.caller.selected))
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, supported⟩ :=
      CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport.of_actual
        stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
        (signature := fixture.makeSignature)
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        (by rw [sameSource]; exact observed.makeRow.sourceOwner)
        shape tree.prepared _ (.anonymous selected)
    exact ⟨⟨packet, CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic _ _ _ supported⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedTypes
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.identity_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.identity_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.identity_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.identityShape.returns]
  rfl

theorem ActualHeader.make_input_types_source {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).1
  rw [observed.makeShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.make_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.make_input_types_source
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) : actual.header.function.resultType = closureType := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _))) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.relay_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.relayShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.relay_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.relay_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.relay_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.relayRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.relayShape.returns]
  rfl

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCertifiedHeaders
/-! The original physical cache slot identifies each automatic catalog Header.
The original public observations retain their complete execution receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open SelectedCompilationCertifiedPublicSession (EligibleRow Issued Initial)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem selected_row (row : ObservedRow fixture signature) :
    ∃ selected : EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨_signatureEq, indexEq⟩ := row.prepared_slot prepared
  refine ⟨⟨prepared.named, row.index, row.global, indexEq ▸ prepared.selected,
    row.slot, row.globalKey, ?_⟩, prepared.same⟩
  rw [prepared.same]
  refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
  simp only [row.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
    List.not_mem_nil, false_implies, implies_true]

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows)
    (specialized : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans specialized)
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation,
      sameRow, row.parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

def firstCall {row : ObservedRow fixture signature} (first : ObservedPublicRun fixture row) :
    SelectedCompilationPublicSessionState.FunctionCall first.session row.row.key [.word seed] runOptions :=
  ⟨⟨⟨first.checkpoint, first.started⟩, first.completion, first.executed⟩, first.handle, first.returned⟩

def functionCall {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments) :
    SelectedCompilationPublicSessionState.FunctionCall session key arguments runOptions :=
  ⟨⟨⟨call.checkpoint, call.started⟩, call.completion, call.executed⟩, call.handle, call.returned⟩

/-- The first successful export keeps the actual requested raw function type. -/
theorem initial_handle_type {issued : Issued fixture.recipe}
    {row : ObservedRow fixture signature} {first : ObservedPublicRun fixture row}
    (initial : Initial issued (firstCall first).toCall.toStartedCall) :
    first.handle.sourceType = initial.header.function.resultType := by
  obtain ⟨checkpoint, started, resumed⟩ := first.executed
  have same : checkpoint = first.checkpoint := Except.ok.inj (started.symm.trans first.started)
  subst checkpoint
  obtain ⟨_actual, _generation, _value, _store, _done, exported, valueEq, _typeEq, _budgetEq, _atSession⟩ :=
    resumed.indexed_succeeded initial.start.atCheckpoint
  have atRecipe : initial.start.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe → artifact.RecipeAt fixture.recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ initial.start.started.recipe_eq
  have requested := initial.start.started.original.result_type_at atRecipe initial.start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result initial.start.selected).2
  rw [resultType] at requested
  exact exported.function_source_type requested (valueEq.symm.trans first.returned)

end Tests.SourceCoreCanonicalScoped.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCertifiedMeaning
/-! The original scoped closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original scoped closure compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) where
  initial : Initial issued (firstCall first).toCall.toStartedCall
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = first.handle
  handleType : first.handle.sourceType = closureType
  after : issued.State initial.header first.completion.session [entry]
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure FunctionMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (stages : ObservedStages fixture observed.makeRow) (value : Core.Word)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.makeRow.row.key [.word value] runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value]
  rawType : request.header.function.resultType = closureType
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = closureType
  after : issued.State anchor call.completion.session (entries ++ [entry])
  trace : SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap [.word value] (.value entry.source) after.heap

def packedSource (next : Core.Word) (flag stop : Bool) : Dynamic.Value :=
  .product (.word next) (.product (.bool flag) (.bool stop))

theorem packed_input (entries : List Entry) (context : SourceSemantics.Context) (next : Core.Word) (flag stop : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context parameterType
      (packed next flag stop) (packedSource next flag stop) := by
  exact .product
    (.data ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
    (.product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
        ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))

structure InvocationMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (next : Core.Word) (flag stop : Bool)
    {handle : SourceCorePublicValues.Handle}
    (call : ObservedInvocation session handle (packed next flag stop))
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = handle
  handleType : handle.sourceType = closureType
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments (packedSource next flag stop)
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨profiled, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    (firstCall first).toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  let issued := profiled.toIssued
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := firstCall first) (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  have raw : initial.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, type.trans raw, handle,
    (initial_handle_type initial).trans raw, after, trace⟩⟩⟩

theorem function_meaning (before : issued.State anchor session entries)
    (stages : ObservedStages fixture observed.makeRow) (value : Core.Word)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) :
    Nonempty (FunctionMeaning issued before stages value call) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before (functionCall call).toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value] := by
    rw [← actualEq, actual.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.reflect_function before (functionCall call)
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

theorem invocation_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = closureType) (next : Core.Word) (flag stop : Bool)
    (call : ObservedInvocation session handle (packed next flag stop))
    (word : Core.Word) (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (InvocationMeaning issued before entry next flag stop call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType)
      (packed_input entries anchor.function.context next flag stop)
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, handleType, arguments, packing, arity, after, size, trace⟩⟩

theorem FirstMeaning.forward {stages : ObservedStages fixture observed.makeRow}
    {first : ObservedPublicRun fixture observed.makeRow} (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support (firstCall first).toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed] meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact meaning.initial.forward_function
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
    (parameter := parameterType) (resultType := .word)
    (by rw [meaning.headerEq, meaning.actual.make_result_type]; rfl) meaning.trace

theorem FunctionMeaning.forward {before : issued.State anchor session entries}
    {stages : ObservedStages fixture observed.makeRow} {value : Core.Word}
    {call : ObservedFunctionCall session observed.makeRow.row.key [.word value]}
    (meaning : FunctionMeaning issued before stages value call) (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      (functionCall call).toCall.toStartedCall parameterType .word meaning.entry.source meaning.after.heap :=
  issued.forward_function before (functionCall call).toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem InvocationMeaning.forward {before : issued.State anchor session entries}
    {entry : Entry} {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle (packed next flag stop) runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (.word word) checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectScalarForward.forward_call issued.support issued.prepared
    before entry meaning.member (.word word) meaning.entryType (meaning.handleEq ▸ meaning.handleType)
    (packed_input entries anchor.function.context next flag stop)
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreCanonicalScoped.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCompilerBody
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedBodyFlow

theorem ActualHeader.relay_body {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.function.body = [observed.relayShape.initialized.id, observed.relayShape.statement.id] := by
  rw [actual.aligned.function]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.relayShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

private theorem returned_child {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr}
    {returned : StatementNode} {expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope [returned.id] code)
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? returned.id = some returned)
    (form : returned.form = .returnStmt (some expression)) :
    tree.children.map (·.expression) = [expression] := by
  cases tree with
  | returning read actualForm =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
      rfl
  | initialized read actualForm | returnUnit read actualForm | absent read actualForm
  | assigning read actualForm | assigned read actualForm | projectedAssigned read actualForm | whileLoop read actualForm
  | bitNotting read actualForm | bitNotted read actualForm | projectedBitNotted read actualForm
  | discard read actualForm | block read actualForm | conditional read actualForm
  | tailValue read actualForm | valueDiscard read actualForm
  | matching read actualForm | matched read actualForm
  | forLoop read actualForm | forBoundary read actualForm | breaking read actualForm | continuing read actualForm =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans found)
      cases same
      simp only [form, expanded] at outside
      cases outside

private theorem let_return {policy : SourceCoreLoops.Policy} {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {result : Ty} {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word}
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {code : Expr} {statements : List StatementId}
    {initialized returned : StatementNode} {binder : TypedBinder} {initializer expression : ExpressionId}
    (tree : Tree policy source result reasonAt mode escaped fuel scope statements code)
    (roots : statements = [initialized.id, returned.id])
    (reader : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (initialFound : source.lookupStatement? initialized.id = some initialized)
    (initialForm : initialized.form = .letDecl binder (some initializer))
    (returnFound : source.lookupStatement? returned.id = some returned)
    (returnForm : returned.form = .returnStmt (some expression)) :
    tree.closed = true ∧ tree.bindings.map (·.binder) = [binder] ∧
      tree.children.map (·.expression) = [initializer, expression] := by
  subst statements
  cases tree with
  | initialized read form _ projected child generated _ remaining allocated =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      rw [initialForm] at form
      cases form
      have tail := remaining.at_return reader returnFound returnForm
      have children := returned_child remaining reader returnFound returnForm
      simp only [Tree.closed, Tree.bindings, Tree.children, List.map_cons, tail.1, tail.2.1,
        List.map_nil, children, and_self]
  | returning read form | returnUnit read form | absent read form
  | assigning read form | assigned read form | projectedAssigned read form | whileLoop read form
  | bitNotting read form | bitNotted read form | projectedBitNotted read form
  | discard read form | block read form | conditional read form
  | valueDiscard read form
  | matching read form | matched read form
  | forLoop read form | forBoundary read form | breaking read form | continuing read form =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp_all
  | boundary read outside accepted =>
      have same := Option.some.inj ((read_found (reader ▸ read)).symm.trans initialFound)
      cases same
      simp only [initialForm, expanded] at outside
      cases outside

/-- Inversion of the actual accepted body preserves the ordered child actions
and original binder. No expression syntax is supplied to this theorem. -/
theorem ActualHeader.relay_compiler_details {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : AcceptedNamedBodyAdmission.BodyAt actual.header) :
    receipt.tree.closed = true ∧
      receipt.tree.bindings.map (·.binder) = [observed.relayShape.localBinder] ∧
      receipt.tree.children.map (·.expression) =
        [observed.relayShape.initial.value.node.id, observed.relayShape.finalRead.node.id] := by
  exact let_return receipt.tree actual.relay_body
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read actual.prepared actual.aligned)
    (by rw [actual.source]; exact observed.relayShape.initializedFound)
    observed.relayShape.initializedForm
    (by rw [actual.source]; exact observed.relayShape.statementFound)
    observed.relayShape.statementForm

theorem ActualHeader.relay_compiler_bindings {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : AcceptedNamedBodyAdmission.BodyAt actual.header) :
    ∀ binding ∈ receipt.tree.bindings,
      RecursiveNamedStatementSyntaxFacts.BinderReceipt actual.header.function.source binding.binder := by
  rcases AcceptedNamedBodyBindings.of_header actual.prepared actual.aligned fixture.source_wellFormed receipt.tree with binders | boundary
  · exact binders
  · obtain ⟨binding, member, quantified⟩ := boundary
    have present := List.mem_map.mpr (show ∃ actual ∈ receipt.tree.bindings, actual.binder = binding.binder from ⟨binding, member, rfl⟩)
    rw [actual.relay_compiler_details receipt |>.2.1] at present
    have same := List.mem_singleton.mp present
    exact False.elim (quantified (by rw [same, observed.relayShape.localScheme]; rfl))

theorem ActualHeader.relay_metadata {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite observed.relayAdmission.table.rows) := by
  rw [(CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data actual.prepared actual.aligned).1,
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared
      observed.relayAdmission.selected observed.relayAdmission.same]
  exact observed.relayAdmission.metadata

theorem ActualHeader.relay_direct_sites {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    RelayDirectSites actual.header.function.source observed.relayAdmission.table.rows := by
  rw [(CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data actual.prepared actual.aligned).1,
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared
      observed.relayAdmission.selected observed.relayAdmission.same]
  exact observed.relayAdmission.sites

theorem ObservedProgram.relay_direct_supported {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ instantiation, CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite
      observed.relayAdmission.table.rows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation := by
  obtain ⟨identityInput, makeInput, relayInput, _identityRow, _makeRow, _relayRow,
    identityPacket, makePacket, relayPacket, _identityHeader, _makeHeader, _relayHeader,
    _identityEq, _makeEq, _relayEq, complete⟩ := observed.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory
      [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have table := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.table_aligned_of_complete
    rows complete observed.relayAdmission.table
  exact fun _ site => site.supported table

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCompilerExpressions
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def RelayReached (observed : ObservedProgram fixture) (id : ExpressionId) : Prop :=
  id = observed.relayShape.initial.value.node.id ∨
    id = observed.relayShape.initialRead.node.id ∨ id = observed.relayShape.finalRead.node.id

theorem ActualHeader.relay_reached_form (actual : ActualHeader fixture observed.relayRow.row)
    {id : ExpressionId} {node : ExpressionNode} (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      (∃ callee instantiation, node.form = .call callee [observed.relayShape.initialRead.node.id]
        (.declaration instantiation)) := by
  rw [actual.source] at found
  rcases reached with same | same | same
  · rw [same, observed.relayShape.initial.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, observed.relayShape.initial.form⟩
  · rw [same, observed.relayShape.initialRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, observed.relayShape.initialRead.form⟩
  · rw [same, observed.relayShape.finalRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, observed.relayShape.finalRead.form⟩

theorem ActualHeader.relay_reached_arguments (actual : ActualHeader fixture observed.relayRow.row)
    {id callee : ExpressionId} {node : ExpressionNode} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    arguments = [observed.relayShape.initialRead.node.id] := by
  rcases actual.relay_reached_form reached found with ⟨name, binder, localForm⟩ | ⟨other, selected, directForm⟩
  · rw [localForm] at form
    cases form
  · cases form.symm.trans directForm
    rfl

variable (actual : ActualHeader fixture observed.relayRow.row)
  {rootFuel : Nat} {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := fixture.recipe.compiled) actual.prepared.named actual.prepared.diagnostics
    actual.prepared.code actual.prepared.compilation rootFuel actual.header.function.source
    rootScope rootId actual.header.reasonAt rootLowered)

private theorem no_method {id : ExpressionId} {node : ExpressionNode}
    (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node)
    (method : MethodForm node.form) : False := by
  rcases actual.relay_reached_form reached found with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
  all_goals
    rcases method with ⟨operator, operand, operatorForm⟩ | ⟨operator, left, right, operatorForm⟩
    all_goals rw [form] at operatorForm; cases operatorForm

private theorem no_cause {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named)
      actual.header.function.source scope id actual.header.reasonAt lowered)
    (reached : RelayReached observed id) (cause : Cause root head) : False := by
  have forms := actual.relay_reached_form reached head.found
  cases cause with
  | form _ notLeaf notDirect _notIndirect _notMethod _notIndex _notConstructor _notComposite _notBuiltin =>
      rcases forms with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
      · exact notLeaf (form ▸ LeafForm.read name binder)
      · exact notDirect ⟨_, _, _, form⟩
  | initializer _ selected =>
      have found := selected.found
      simp only [observed.noLocals, List.find?_nil, Option.filter_none] at found
      cases found
  | special selected outside _outsideMethod =>
      rcases forms with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
      · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy
          actual.relay_metadata head.found (.inr ⟨name, binder, form⟩)
          (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child
            root.selected.policy root.selected.lowerBody fuel
            (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named))
          (fuel + 1) scope actual.header.reasonAt
        have same := head.selected.symm.trans profile.2.2
        rw [selected] at same
        cases same
      · exact outside ⟨_, _, _, form⟩
  | indexOperands _ form _ | constructorRange _ form _ =>
      rcases forms with ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | operatorCoercions _ operator _ =>
      exact no_method actual reached head.found operator

private theorem children_reached {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (step : Step root actual.header.function.source scope actual.header.reasonAt fuel id lowered)
    (reached : RelayReached observed id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : RelayReached observed entry.1 := by
  cases step with
  | leaf => cases member
  | proxy => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
      have args := actual.relay_reached_arguments reached receipt.metadata.found receipt.form
      have present := (List.of_mem_zip member).1
      rw [args] at present
      exact .inr (.inl (List.mem_singleton.mp present))
  | evidence head _ receipt =>
      have args := actual.relay_reached_arguments reached head.found receipt.form
      have present := (List.of_mem_zip member).1
      rw [args] at present
      exact .inr (.inl (List.mem_singleton.mp present))
  | indirect _head _plain receipt =>
      have form := receipt.originalForm
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | index _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | constructor _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | composite _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | primitive _ _ receipt =>
      exact False.elim (no_method actual reached receipt.found receipt.form)
  | builtin _ _ receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.metadata.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form; cases form
      · rw [directForm] at form; cases form
  | method _head _selected receipt =>
      apply False.elim
      apply no_method actual reached receipt.metadata.found
      rcases receipt.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩

/-- Only accepted argument edges are followed. The stored declaration callee
is preserved in Source, but is never substituted for an executed child. -/
theorem ActualHeader.relay_boundary_impossible {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : Trace root actual.header.function.source scope actual.header.reasonAt fuel id lowered}
    (boundary : Boundary tree) (reached : RelayReached observed id) : False := by
  induction boundary with
  | here head cause children => exact no_cause actual root head reached cause
  | child step children entry member next ih =>
      exact ih (children_reached actual root step reached member)

theorem ActualHeader.relay_expression_residual_impossible
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (reached : RelayReached observed id)
    (residual : Residual actual.prepared actual.header
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite observed.relayAdmission.table.rows)
      fuel actual.header.function.source scope id lowered) : False :=
  actual.relay_boundary_impossible residual.root residual.boundary reached

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCompilerProfile
/-! One actual complete compiler profile connects the unchanged six public
calls to Source execution, retained captures and all sufficient fuel bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  second : FunctionMeaning issued first.after stages secondSeed sequence.second
  firstRead : InvocationMeaning issued second.after first.entry firstNext true false
    sequence.firstRead seed (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : FunctionMeaning issued firstRead.after stages interveningSeed sequence.intervening
  secondRead : InvocationMeaning issued intervening.after second.entry secondNext true false
    sequence.secondRead secondSeed (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  repeatedRead : InvocationMeaning issued secondRead.after first.entry repeatedNext false false
    sequence.repeatedRead seed (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Issued fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.handles_distinct (meaning : SequenceMeaning issued stages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq]
  exact sequence.distinct

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨second⟩ := function_meaning first.after stages secondSeed sequence.second
  obtain ⟨firstRead⟩ := invocation_meaning second.after first.entry (by simp)
    first.entryType first.handleEq first.handleType firstNext true false sequence.firstRead seed sequence.firstValue scope
  obtain ⟨intervening⟩ := function_meaning firstRead.after stages interveningSeed sequence.intervening
  obtain ⟨secondRead⟩ := invocation_meaning intervening.after second.entry (by simp)
    second.entryType second.handleEq second.handleType secondNext true false sequence.secondRead secondSeed sequence.secondValue scope
  obtain ⟨repeatedRead⟩ := invocation_meaning secondRead.after first.entry (by simp)
    first.entryType first.handleEq first.handleType repeatedNext false false sequence.repeatedRead seed sequence.repeatedValue scope
  exact ⟨issued, ⟨⟨first, second, firstRead, intervening, secondRead, repeatedRead⟩⟩⟩

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (functionCall sequence.second).toCall.toStartedCall parameterType .word meaning.second.entry.source meaning.second.after.heap
  firstRead : ∃ checkpoint, sequence.second.completion.session.startHandlePacked sequence.first.handle
      (packed firstNext true false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe ([meaning.first.entry] ++ [meaning.second.entry])
      (.word seed) checkpoint meaning.firstRead.after.heap
  intervening : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt
    (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (functionCall sequence.intervening).toCall.toStartedCall parameterType .word meaning.intervening.entry.source meaning.intervening.after.heap
  secondRead : ∃ checkpoint, sequence.intervening.completion.session.startHandlePacked sequence.second.handle
      (packed secondNext true false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.intervening.entry])
      (.word secondSeed) checkpoint meaning.secondRead.after.heap
  repeatedRead : ∃ checkpoint, sequence.secondRead.completion.session.startHandlePacked sequence.first.handle
      (packed repeatedNext false false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.intervening.entry])
      (.word seed) checkpoint meaning.repeatedRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady interveningReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstRead.forward secondReady,
    meaning.intervening.forward firstReadReady, meaning.secondRead.forward interveningReady,
    meaning.repeatedRead.forward secondReadReady⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧ ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  exact ⟨issued, meaning, meaning.handles_distinct, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.value.table.rows.length == 3 do
    throw (IO.userError "scoped closure profile changed original cache3/table3")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.intervening.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize]
  unless stores == [4,10,16,53,59,96,124] do
    throw (IO.userError s!"scoped closure profile stores changed: {reprStr stores}")
  IO.println "SCOPED_CLOSURE_PROFILE_FORWARD_PASS: original C6 at checker1000; one complete profile and automatic catalog; make10/make20/A10/make30/B20/A10; retained captures and related Source heaps; all six sufficient public fuel bounds; original stores"

end Tests.SourceCoreCanonicalScoped.CompilerProfile
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedRelaySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

/-- Both the statement tree and its ordered expression actions come from the
actual accepted compiler body. The original finite metadata remains explicit. -/
theorem ActualHeader.relay_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header
      observed.relayAdmission.table.rows := by
  rcases AcceptedNamedBodyExpressionAdmission.of_actual actual.prepared actual.aligned
      actual.relay_metadata observed.relay_direct_supported actual.relay_direct_sites
      fixture.source_wellFormed with admission | unsupported
  · exact admission
  · obtain ⟨unsupported⟩ := unsupported
    cases unsupported with
    | «structure» receipt outside =>
        rw [(actual.relay_compiler_details receipt).1] at outside
        cases outside
    | generalized receipt binding member quantified =>
        have present := List.mem_map.mpr
          (show ∃ selected ∈ receipt.tree.bindings, selected.binder = binding.binder from ⟨binding, member, rfl⟩)
        rw [(actual.relay_compiler_details receipt).2.1] at present
        have same := List.mem_singleton.mp present
        exact False.elim (quantified (by rw [same, observed.relayShape.localScheme]; rfl))
    | expression receipt child member residual =>
        have present := List.mem_map.mpr
          (show ∃ selected ∈ receipt.tree.children, selected.expression = child.expression from ⟨child, member, rfl⟩)
        rw [(actual.relay_compiler_details receipt).2.2] at present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        have reached : RelayReached observed child.expression := by
          rcases present with initial | final
          · exact .inl initial
          · exact .inr (.inr final)
        exact False.elim (actual.relay_expression_residual_impossible reached residual)

/-- This is the same evidence certificate consumed by the existing public
family. Its Source admission is derived from the compiler action. -/
def ActualHeader.relay_certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedNamedEvidenceAdmission.Certificate fixture.recipe.compiled observed.relayAdmission.named := {
  table := observed.relayAdmission.table
  sourceAdmission := AcceptedNamedBodyAdmission.source_of_header actual.prepared actual.aligned
    observed.relayAdmission.selected observed.relayAdmission.same actual.relay_admission
  requirements := observed.relayAdmission.requirements }

theorem ActualHeader.relay_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  exact CallableIndexedOwnedPreparedNamedEvidenceAdmission.receipt
    actual.prepared actual.aligned observed.relayAdmission.selected observed.relayAdmission.same
    actual.relay_certificate

def ActualHeader.relay_bundle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.relayRow.row, prepared := actual.prepared,
  instantiation := CallableNamedMetadata.instantiation observed.relayRow.row,
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .canonicalBranching receipt }

def ActualHeader.relay_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  exact CallableIndexedOwnedPreparedNamedEvidenceAdmission.of_receipt
    actual.prepared actual.aligned observed.relayAdmission.selected observed.relayAdmission.same
    actual.relay_certificate rows complete fixture.recipePrepared actual.diagnostic
    receiver fixture.source_wellFormed (bootstrap_zero fixture.recipe.compiled)
    observed.relayRow.entryMember receipt stagePrepared

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
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

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [identityHeader.header, makeHeader.header, relayHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  have headerKey := (selected_key selected).trans key
  rcases List.mem_cons.mp selected.member with same | rest
  · rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.identityRow.keys_ne observed.makeRow observed.identityMake headerKey)
  · rcases List.mem_cons.mp rest with same | rest
    · exact same
    · have same := List.mem_singleton.mp rest
      rw [same, relayHeader.key] at headerKey
      exact False.elim (observed.makeRow.keys_ne observed.relayRow observed.makeRelay headerKey.symm)

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

theorem selected_make_at {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [identityHeader.header, makeHeader.header, relayHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make_root identityHeader makeHeader relayHeader request.selected (started_key request)


end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSourceOutcomes
/-! Independent Dynamic outcomes for the original six-call scoped closure
session, including all three packed calls on retained captured closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.SourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CompilerProfile
open SelectedCompilationCertifiedPublicSession (Issued)
open SelectedCompilationPublicSessionState (PlainValue)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

/-- The original packing, arity and retained entry remain in the indexed
meaning; this projection preserves its exact arguments and before/after heaps. -/
def DirectValue
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {before : issued.State anchor session entries} {entry : RecursiveNamedPublicFunctionHistory.Entry}
    {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope) : Prop :=
  Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context scope.evidence (Staging.Recursive.callableEvidence entry.source)
    before.heap entry.source meaning.arguments (.word word) meaning.after.heap

theorem direct_value
    {anchor : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {before : issued.State anchor session entries} {entry : RecursiveNamedPublicFunctionHistory.Entry}
    {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope) : DirectValue meaning :=
  meaning.trace.sound.value_plain

structure DynamicMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  second : PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.second.request.header.function)
    meaning.first.after.heap [.word secondSeed] meaning.second.entry.source meaning.second.after.heap
  firstRead : DirectValue meaning.firstRead
  intervening : PlainValue meaning.first.initial.header meaning.intervening.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.intervening.request.header.function)
    meaning.firstRead.after.heap [.word interveningSeed] meaning.intervening.entry.source meaning.intervening.after.heap
  secondRead : DirectValue meaning.secondRead
  repeatedRead : DirectValue meaning.repeatedRead

theorem dynamic_meaning (meaning : SequenceMeaning issued stages sequence) : DynamicMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, direct_value meaning.firstRead,
    meaning.intervening.trace.value_plain, direct_value meaning.secondRead, direct_value meaning.repeatedRead⟩

theorem closed_outcomes (profile : CompilerProfile.Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      DynamicMeaning meaning ∧ meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      CompilerProfile.ForwardMeaning meaning := by
  obtain ⟨issued, meaning, distinct, forward⟩ := CompilerProfile.closed_sequence_forward_meaning profile stages sequence
  exact ⟨issued, meaning, dynamic_meaning meaning, distinct, forward⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← CompilerProfile.observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _outcomes := closed_outcomes profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.value.table.rows.length == 3 do
    throw (IO.userError "scoped source outcomes changed original cache3/table3")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.intervening.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize]
  unless stores == [4,10,16,53,59,96,124] do
    throw (IO.userError s!"scoped source outcomes changed original stores: {reprStr stores}")
  IO.println "SCOPED_SOURCE_OUTCOMES_PASS: original C6 at checker1000; six independent Dynamic applications; three exact packed retained-closure calls; make10/make20/A10/make30/B20/A10; captured values, reached heaps and all six forward bounds"

end Tests.SourceCoreCanonicalScoped.SourceOutcomes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  identityInput : Input fixture.recipe.compiled
  makeInput : Input fixture.recipe.compiled
  relayInput : Input fixture.recipe.compiled
  identityRow : identityInput.row = observed.identityRow.row
  makeRow : makeInput.row = observed.makeRow.row
  relayRow : relayInput.row = observed.relayRow.row
  identityPacket : Issued identityInput
  makePacket : Issued makeInput
  relayPacket : Issued relayInput
  identityHeader : ActualHeader fixture observed.identityRow.row
  makeHeader : ActualHeader fixture observed.makeRow.row
  relayHeader : ActualHeader fixture observed.relayRow.row
  identityEq : identityHeader.header = identityPacket.header
  makeEq : makeHeader.header = makePacket.header
  relayEq : relayHeader.header = relayPacket.header
  rows : Inventory [identityInput, makeInput, relayInput]
  rowsEq : rows = .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([identityInput, makeInput, relayInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  relayDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.identityHeader.header, support.makeHeader.header, support.relayHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.identityEq, support.makeEq, support.relayEq]

private def selectThree {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second third : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (firstSecond : first.slot ≠ second.slot) (firstThird : first.slot ≠ third.slot)
    (secondThird : second.slot ≠ third.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second) (thirdValue : property third) :
    ∀ header, header ∈ [first, second, third] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (firstSecond (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstThird (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else if secondSlot : header.slot = second.slot then
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (secondThird (secondSlot.symm.trans other))
    exact same.symm ▸ secondValue
  else
    have same : header = third := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ thirdValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨identityInput, makeInput, relayInput, identityRow, makeRow, relayRow,
    identityPacket, makePacket, relayPacket, identityHeader, makeHeader, relayHeader,
    identityEq, makeEq, relayEq, complete⟩ := observed.inventory
  let rows : Inventory [identityInput, makeInput, relayInput] :=
    .cons identityPacket (.cons makePacket (.cons relayPacket .nil))
  have headerList : headers rows = [identityHeader.header, makeHeader.header, relayHeader.header] := by
    simp only [rows, headers, identityEq, makeEq, relayEq]
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have identityInputIndex : identityHeader.header.slot = identityInput.prepared.index := by
    rw [identityEq]; exact identityPacket.aligned.slot
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have relayIndex : relayHeader.header.slot = observed.relayRow.index :=
    relayHeader.aligned.slot.trans (observed.relayRow.prepared_slot relayHeader.prepared).2
  have relayInputIndex : relayHeader.header.slot = relayInput.prepared.index := by
    rw [relayEq]; exact relayPacket.aligned.slot
  have identityMake : identityHeader.header.slot ≠ makeHeader.header.slot := by
    rw [identityIndex, makeIndex]
    exact observed.identityMake
  have identityMakeInput : identityInput.prepared.index ≠ makeInput.prepared.index := by
    rw [← identityInputIndex, ← makeInputIndex]
    exact identityMake
  have identityRelay : identityHeader.header.slot ≠ relayHeader.header.slot := by
    rw [identityIndex, relayIndex]
    exact observed.identityRelay
  have identityRelayInput : identityInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← identityInputIndex, ← relayInputIndex]
    exact identityRelay
  have makeRelay : makeHeader.header.slot ≠ relayHeader.header.slot := by
    rw [makeIndex, relayIndex]
    exact observed.makeRelay
  have makeRelayInput : makeInput.prepared.index ≠ relayInput.prepared.index := by
    rw [← makeInputIndex, ← relayInputIndex]
    exact makeRelay
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.expression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint receiver (fun _ _ proof => proof) (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨identityTerminal, _identityExpression, identitySupport⟩ :=
    identityHeader.identity_support observed receiver (actualStagePrepared fixture)
  obtain ⟨identitySupport⟩ := identitySupport
  obtain ⟨relayReceipt⟩ := relayHeader.relay_receipt
  let relayBody := relayHeader.relay_bundle relayReceipt
  let relaySupport := relayHeader.relay_support rows complete relayReceipt (registry := registry) receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectThree identityMake identityRelay makeRelay property
      ⟨of_terminal identityTerminal, .recursive identitySupport⟩ ⟨of_terminal makeTerminal, makeSupport⟩
      ⟨relayBody, relaySupport⟩ header (headerList ▸ member)
  exact ⟨{
    identityInput := identityInput
    makeInput := makeInput
    relayInput := relayInput
    identityRow := identityRow
    makeRow := makeRow
    relayRow := relayRow
    identityPacket := identityPacket
    makePacket := makePacket
    relayPacket := relayPacket
    identityHeader := identityHeader
    makeHeader := makeHeader
    relayHeader := relayHeader
    identityEq := identityEq
    makeEq := makeEq
    relayEq := relayEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [identityMakeInput, identityRelayInput, makeRelayInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family identityHeader makeHeader relayHeader extra rows complete (actualStagePrepared fixture) receiver association
    identityDescriptor := identityHeader.descriptor identityStages
    makeDescriptor := makeHeader.descriptor makeStages
    relayDescriptor := relayHeader.descriptor relayStages }⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.makeHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedInvocation
/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      started, _parameterView, _resultView, succeeded, actualAt, packing, trace, result,
      _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.terminals
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function parameter .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨sources, next, packing, sourceSize, by simpa only [outcomeValue] using trace⟩


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, _diagnostics, _started, _parameterView, _resultView,
    _succeeded, actualAt, packing, trace, _resultAt, _nativeValue, selected, _handles, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryOutputCollection.public_invoke_succeeded_collects
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.terminals
      support.supports fixture.source_wellFormed state.history entry member entryType input state.atRecipe
      state.registry state.atSession (by simpa only [entryHandle] using call.executed) .skip invocation
  have addedNil : added = [] := by
    simpa only [RecursiveNamedPublicNestedOutputSelections.Selection.handles, List.map_eq_nil_iff] using _handles
  subst added
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := by simpa only [List.append_nil, PublicSupports.functions] using retained }
  exact ⟨sources, source, next, packing, sourceSize, trace⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = closureType ∧ entry.handle = call.handle ∧
      call.handle.sourceType = closureType ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_make_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.makeHeader.make_input_types_source]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.makeDescriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving)
      (receiver := state.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension)
      (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _)
      (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact
    session := actual.session
    mapping := mapping
    world := world
    heap := heap
    store := finalStore
    caller := caller
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := by
      have registered := request.started.returned_registry succeeded
      rw [registryAt] at registered
      exact registered
    history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = closureType
    rw [selected]
    exact support.makeHeader.make_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.make
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = closureType ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.make_typed_handle call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = closureType ∧ entry.handle = first.handle ∧
      first.handle.sourceType = closureType ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types_source]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.makeHeader.header support.makeInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.makePacket.header.named.specialized support.makeInput.prepared.available)) := by
    rw [support.makeEq]
    exact support.makePacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
      first.started first.executed first.returned support.makeDescriptor
  let entry : Entry := ⟨support.makeHeader.header.function.resultType, source, first.handle,
    payload, support.makeHeader.header.output, runOptions.outputValidationFuel⟩
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.completion.session [entry] := {
    artifact := artifact
    session := returnedCompletion.session
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
    history := retained }
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.makeHeader.make_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.makeInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = closureType ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedPublicExecution
/-! Three actual factory calls and three later handle calls with direct bodies keep
all returned sessions and captured Source heaps in one ordered history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  intervening : Entry
  firstType : first.sourceType = closureType
  secondType : second.sourceType = closureType
  interveningType : intervening.sourceType = closureType
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  interveningHandle : intervening.handle = sequence.intervening.handle
  firstHandleType : sequence.first.handle.sourceType = closureType
  secondHandleType : sequence.second.handle.sourceType = closureType
  distinct : first.handle ≠ second.handle
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  firstReadState : RetainedState support sequence.firstRead.completion.session [first, second]
  interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening]
  secondReadState : RetainedState support sequence.secondRead.completion.session [first, second, intervening]
  finalState : RetainedState support sequence.repeatedRead.completion.session [first, second, intervening]
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  firstArguments : List Dynamic.Value
  firstPacking : Dynamic.ValuesPack firstArguments (.product (.word firstNext) (.product (.bool true) (.bool false)))
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondState.heap first.source firstArguments (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondArguments : List Dynamic.Value
  secondPacking : Dynamic.ValuesPack secondArguments (.product (.word secondNext) (.product (.bool true) (.bool false)))
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap second.source secondArguments (.value (.word secondSeed)) secondReadState.heap
  repeatedArguments : List Dynamic.Value
  repeatedPacking : Dynamic.ValuesPack repeatedArguments (.product (.word repeatedNext) (.product (.bool false) (.bool false)))
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap first.source repeatedArguments (.value (.word seed)) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra identityStages makeStages relayStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle sequence.second scope
  have packedInput : ∀ entries next flag stop, RecursiveNamedPublicFunctionHistoryInputs.Input
      entries support.makeHeader.header.function.context parameterType (packed next flag stop)
        (.product (.word next) (.product (.bool flag) (.bool stop))) := by
    intro entries next flag stop
    exact .product
      (.data ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
        ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
      (.product
        (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
          ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
        (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
          ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))
  obtain ⟨firstArguments, firstReadState, firstPacking, firstReadTrace⟩ := invoke_word secondState first
    (by simp) firstType firstHandle firstHandleType (packedInput _ firstNext true false) sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.make_typed_handle sequence.intervening scope
  obtain ⟨secondArguments, secondReadState, secondPacking, secondReadTrace⟩ := invoke_word interveningState second
    (by simp) secondType secondHandle secondHandleType (packedInput _ secondNext true false) sequence.secondRead sequence.secondValue scope
  obtain ⟨repeatedArguments, finalState, repeatedPacking, repeatedReadTrace⟩ := invoke_word secondReadState first
    (by simp) firstType firstHandle firstHandleType (packedInput _ repeatedNext false false) sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, firstHandleType, secondHandleType,
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    initial, secondState, firstReadState, interveningState, secondReadState, finalState,
    firstTrace, secondTrace, firstArguments, firstPacking, firstReadTrace,
    interveningTrace, secondArguments, secondPacking, secondReadTrace,
    repeatedArguments, repeatedPacking, repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra identityStages makeStages relayStages sequence receiver⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedInitialForward
/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel closureType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world closureType source payload nativeType

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after ∧ ReturnedValue completion returned source outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.identityHeader support.makeHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types_source]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.makeHeader.make_result_type] at requested
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  have checkpointReady := started.original.initial_registry.exportsReady (sessionAt.exportsReady_iff.mp initialReady)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded checkpointAt resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions _finalMap _finalWorld closureType source _payload support.makeHeader.header.output := by
    have result := _fullResult.2.1
    rw [support.makeHeader.make_result_type] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl, _payload, _, encoded, represented⟩



end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedInvocationForward
/-! The three captured closure calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = closureType)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = closureType)
    {next : Core.Word} {flag stop : Bool} {word : Core.Word}
    (call : ObservedInvocation publicSession handle (packed next flag stop))
    (exportsReady : publicSession.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {arguments : List Dynamic.Value}
    (packing : Dynamic.ValuesPack arguments (.product (.word next) (.product (.bool flag) (.bool stop))))
    (trace : SourceInvocation support invocation state.heap entry.source arguments (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle (packed next flag stop) word after := by
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .word (.word next) (.word next) :=
    .data ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
  have boolInput (value : Bool) : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context .bool (.bool value) (.bool value) :=
    .data ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩
      ⟨.bool value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool value⟩
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameterType (packed next flag stop)
      (.product (.word next) (.product (.bool flag) (.bool stop))) :=
    .product wordInput (.product (boolInput flag) (boolInput stop))
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have signature := started.selected.signature handleType
  have requested := started.requested_exact handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  subst nativeResult
  rw [← entryHandle] at started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨size, trace⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      support.terminals
      support.supports fixture.source_wellFormed state.history entry member entryType
      input state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started packing trace atCheckpoint
  have payloadEq : payload = .word word := by
    have represented := fullResult.1
    cases represented with
    | value related =>
      obtain ⟨actual, sourceEq, nativeEq⟩ := CompatibleExpressionPrimitives.word_fields related
      cases Dynamic.Value.word.inj sourceEq
      exact nativeEq
  subst payload
  refine ⟨publicCheckpoint, accepted, requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, atCompletion,
      _related, history, returnedRegistry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome enoughExecution enoughOutput resumed
  have valueEq : completion.value = .word word := atCompletion.1.trans (exported.word_value requested)
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := atCompletion.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := history }
  exact ⟨completion, succeeded, valueEq, atCompletion.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

/-- All three genuine closure invocations preserve their Source heap at
all sufficient public execution/output budgets on the original starts. -/
def InvocationForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  ForwardWordAt meaning.support sequence.second.completion.session [meaning.first, meaning.second]
    sequence.first.handle (packed firstNext true false) seed meaning.firstReadState.heap ∧
  ForwardWordAt meaning.support sequence.intervening.completion.session [meaning.first, meaning.second, meaning.intervening]
    sequence.second.handle (packed secondNext true false) secondSeed meaning.secondReadState.heap ∧
  ForwardWordAt meaning.support sequence.secondRead.completion.session [meaning.first, meaning.second, meaning.intervening]
    sequence.first.handle (packed repeatedNext false false) seed meaning.finalState.heap

theorem SequenceWitness.invocations_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : InvocationForwardMeaning meaning := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady interveningReady
  exact ⟨forward_word meaning.secondState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.firstRead secondReady
      meaning.firstPacking meaning.firstReadTrace,
    forward_word meaning.interveningState meaning.second (by simp)
      meaning.secondType meaning.secondHandle meaning.secondHandleType sequence.secondRead interveningReady
      meaning.secondPacking meaning.secondReadTrace,
    forward_word meaning.secondReadState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType sequence.repeatedRead secondReadReady
      meaning.repeatedPacking meaning.repeatedReadTrace⟩

end Tests.SourceCoreCanonicalScoped
end

section
-- leanmerge: from Solcore.Test.SourceCoreCanonicalScopedForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value])
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after ∧
          ReturnedValue completion returned source outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.identityInput, support.makeInput, support.relayInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.identityHeader support.makeHeader support.relayHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  have sourceAt' : CallableIndexedOwnedFunctionValues.NamedSourceAt request.header rawD function := by
    rw [selectedHeader]; exact sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.identityInput, support.makeInput, support.relayInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt') applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.makeHeader.make_result_type] at requested
  have checkpointReady := request.started.original.initial_registry.exportsReady (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound (Nat.le_trans (Nat.le_max_left _ _) outputBound) resumed
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded request.atCheckpoint resumed checkpointReady
      (_nativeEnough executionFuel executionBound) requested rfl (by omega)
  have sameCompletion : exportedCompletion = completion := SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  have represented : CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked receiving.result.context.registry
      support.functions finalMap finalWorld closureType source payload request.header.output := by
    have result := fullResult.2.1
    have rawType : request.header.function.resultType = closureType := by rw [selectedHeader]; exact support.makeHeader.make_result_type
    rw [rawType] at result
    cases result with | value represented => exact represented
  have encoded := (exported.reimports_payload requested rfl).2
  rw [← actualAt.1] at encoded
  exact ⟨completion, succeeded, handle, functionValue, handleType,
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl, payload, _, encoded, represented⟩


/-- All three factory executions have independent Source-to-public
bounds, at their exact original checkpoints and current captured heaps. -/
def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.intervening
    meaning.intervening.source meaning.interveningState.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have readReady := sequence.firstRead.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_make meaning.initial sequence.second firstReady meaning.secondTrace,
    forward_make meaning.firstReadState sequence.intervening readReady meaning.interveningTrace⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (identityStages : ObservedStages fixture observed.identityRow)
    (makeStages : ObservedStages fixture observed.makeRow)
    (relayStages : ObservedStages fixture observed.relayRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver, ForwardMeaning meaning ∧ InvocationForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ := closed_sequence_meaning fixture observed extra identityStages makeStages relayStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward, meaning.invocations_forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let identityStages ← observeStages fixture observed.identityRow
  let makeStages ← observeStages fixture observed.makeRow
  let relayStages ← observeStages fixture observed.relayRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra identityStages makeStages relayStages sequence
  IO.println "Scoped direct relay: make10/make20/A10/make30/B20/A10, exact Source heaps/history, all six public fuel bounds proved"

end Tests.SourceCoreCanonicalScoped
end
