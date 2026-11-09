import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PatternsAndArms

/-!
# Captured closure branch tests

Closures with captured values in branches and matches.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchSource
/-! Independent Source typing for a closure with scoped conditional writes and early return. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics

structure Read (source : TypedSource) (binder : TypedBinder) (expected : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference binder.name (.local binder.id)
  raw : node.rawType = expected
  type : node.type = expected
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Read.typed {source : TypedSource} {binder : TypedBinder} {expected : TypeSystem.Ty}
    (read : Read source binder expected) {context : SourceSemantics.Context}
    (scheme : binder.scheme = .mono expected) (requirements : binder.schemeRequirements = [])
    (word : TypeAdmissible context expected)
    (lookup : context.LocalLookup binder.id binder.scheme)
    (localRequirements : context.LocalSchemeRequirementsLookup binder.id binder.schemeRequirements) :
    ExpressionHasType source context read.node.id expected := by
  have instantiated : LocalSchemeInstantiationValid context binder expected [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ requirements)
      (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply expected
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, requirements]
      exact .nil
  have typed : ExpressionHasType source context read.node.id read.node.type := by
    refine .intro (lookupExpression?_sound read.found)
      (read.form ▸ ExpressionFormHasRawType.reference (.local lookup localRequirements instantiated))
      read.raw word (Eq.mp (congrArg (TypeAdmissible context) read.type.symm) word) ?_
    rw [read.requirements, read.coercions, read.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context read.node.id type) read.type) typed

abbrev WordRead (source : TypedSource) (binder : TypedBinder) := Read source binder .word
abbrev BoolRead (source : TypedSource) (binder : TypedBinder) := Read source binder .bool

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  flag : TypedBinder
  argument : TypedBinder
  previous : TypedBinder
  conditionRead : BoolRead function.typedBody flag
  earlyConditionRead : BoolRead function.typedBody flag
  initialRead : WordRead function.typedBody binder
  argumentRead : WordRead function.typedBody argument
  previousRead : WordRead function.typedBody previous
  earlyRead : WordRead function.typedBody binder
  finalRead : WordRead function.typedBody binder
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  elseAssignment : StatementNode
  elseResolution : AssignmentResolution
  branch : StatementNode
  earlyReturn : StatementNode
  earlyBranch : StatementNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOwner : flag.id.owner = function.typedBody.owner
  flagDistinct : flag.id ≠ binder.id
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentDistinct : argument.id ≠ binder.id
  argumentFlag : argument.id ≠ flag.id
  parameterNames : flag.name ≠ argument.name
  previousScheme : previous.scheme = .mono .word
  previousRequirements : previous.schemeRequirements = []
  previousOwner : previous.id.owner = function.typedBody.owner
  previousDistinct : previous.id ≠ binder.id
  previousArgument : previous.id ≠ argument.id
  previousFlag : previous.id ≠ flag.id
  previousOrdinary : previous.comptime = false
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function (.product .bool .word) .word]
  inputs : function.typedBody.inputs = [binder]
  binderOwner : binder.id.owner = function.typedBody.owner
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl previous (some initialRead.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal argumentRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  elseAssignmentFound : function.typedBody.lookupStatement? elseAssignment.id = some elseAssignment
  elseAssignmentForm : elseAssignment.form = .assignValue elseResolution .equal previousRead.node.id
  elseAssignmentType : elseAssignment.type = .unit
  elseTargetRoot : elseResolution.target.root = binder.id
  elseTargetType : elseResolution.target.type = .word
  elseTargetBare : elseResolution.target.projections = []
  elseAssignmentRequirements : elseResolution.requirements = []
  branchFound : function.typedBody.lookupStatement? branch.id = some branch
  branchForm : branch.form = .ifThen conditionRead.node.id [assignment.id] (some [initialized.id, elseAssignment.id])
  branchType : branch.type = .unit
  earlyReturnFound : function.typedBody.lookupStatement? earlyReturn.id = some earlyReturn
  earlyReturnForm : earlyReturn.form = .returnStmt (some earlyRead.node.id)
  earlyReturnType : earlyReturn.type = .word
  earlyBranchFound : function.typedBody.lookupStatement? earlyBranch.id = some earlyBranch
  earlyBranchForm : earlyBranch.form = .ifThen earlyConditionRead.node.id [earlyReturn.id] none
  earlyBranchType : earlyBranch.type = .unit
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some finalRead.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [flag, argument] .word [branch.id, earlyBranch.id, innerReturn.id]
  expressionRaw : expression.rawType = .function (.product .bool .word) .word
  expressionType : expression.type = .function (.product .bool .word) .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function (.product .bool .word) .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.branch.id, shape.earlyBranch.id, shape.innerReturn.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node,
    .expression shape.argumentRead.node,
    .statement shape.assignment,
    .expression shape.initialRead.node,
    .statement shape.initialized,
    .expression shape.previousRead.node,
    .statement shape.elseAssignment,
    .statement shape.branch,
    .expression shape.earlyConditionRead.node,
    .expression shape.earlyRead.node,
    .statement shape.earlyReturn,
    .statement shape.earlyBranch,
    .expression shape.finalRead.node,
    .statement shape.innerReturn,
    .expression shape.expression,
    .statement shape.statement]

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

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .function (.product .bool .word) .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
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
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
    have callable : TypeAdmissible lexical (.function (.product .bool .word) .word) :=
      ⟨binders, .function (.product (.builtin .bool) (.builtin .word)) (.builtin .word)⟩
    let flags := lexical.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
    have flagExtended : BinderExtends function.typedBody.owner lexical shape.flag flags := by
      apply BinderExtends.intro
      · exact {
          owned := shape.flagOwner
          scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible bool
          quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.flagRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.flagDistinct]
    have flagWord : TypeAdmissible flags .word := ⟨binders, .builtin .word⟩
    let arguments := flags.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner flags shape.argument arguments := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible flagWord
          quantified_fresh := by rw [shape.argumentScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.argumentRequirements }
      · cases head
        simp [flags, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.argumentDistinct, shape.argumentFlag]
    have argumentWord : TypeAdmissible arguments .word := ⟨binders, .builtin .word⟩
    have argumentBool : TypeAdmissible arguments .bool := ⟨binders, .builtin .bool⟩
    let locals := arguments.withLocal shape.previous.id shape.previous.scheme shape.previous.schemeRequirements
    have previousExtended : BinderExtends function.typedBody.owner arguments shape.previous locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.previousOwner
          scheme := shape.previousScheme.symm ▸ SchemeWellFormed.monoAdmissible argumentWord
          quantified_fresh := by rw [shape.previousScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.previousRequirements }
      · cases head
        simp [arguments, flags, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.previousDistinct, shape.previousArgument, shape.previousFlag]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have seedLookup : arguments.LocalLookup shape.binder.id shape.binder.scheme :=
      .tail shape.argumentDistinct (.tail shape.flagDistinct head.local_self)
    have seedRequirements : arguments.LocalSchemeRequirementsLookup shape.binder.id shape.binder.schemeRequirements :=
      .tail shape.argumentDistinct (.tail shape.flagDistinct head.local_scheme_requirements_self)
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements argumentBool
      (.tail shape.argumentFlag flagExtended.local_self) (.tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
    have earlyConditionTyped := shape.earlyConditionRead.typed shape.flagScheme shape.flagRequirements argumentBool
      (.tail shape.argumentFlag flagExtended.local_self) (.tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
    have initialTyped := shape.initialRead.typed scheme shape.binderRequirements argumentWord seedLookup seedRequirements
    have rhsTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements argumentWord
      argumentExtended.local_self argumentExtended.local_scheme_requirements_self
    have previousTyped := shape.previousRead.typed shape.previousScheme shape.previousRequirements localWord
      previousExtended.local_self previousExtended.local_scheme_requirements_self
    have earlyTyped := shape.earlyRead.typed scheme shape.binderRequirements argumentWord seedLookup seedRequirements
    have finalTyped := shape.finalRead.typed scheme shape.binderRequirements argumentWord seedLookup seedRequirements
    have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ arguments shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.previousScheme, TypeSystem.Scheme.mono] using initialTyped
      · rw [shape.previousScheme]; rfl
      · rw [shape.previousScheme]; rfl
      · exact previousExtended
      · exact shape.initializedType
    have writable : WritableLocal arguments shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro seedLookup (scheme.symm ▸ SchemeWellFormed.monoAdmissible argumentWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody arguments shape.resolution .equal shape.argumentRead.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word, 0⟩ arguments shape.assignment.id arguments ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have elseWritable : WritableLocal locals shape.elseResolution.target.root .word := by
      rw [shape.elseTargetRoot]
      exact .intro (.tail shape.previousDistinct seedLookup) (scheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have elseAssignmentTyped : SourceAssignmentHasType function.typedBody locals shape.elseResolution .equal shape.previousRead.node.id :=
      .equal (.intro elseWritable (by rw [shape.elseTargetBare]; exact .nil _) shape.elseTargetType) previousTyped shape.elseAssignmentRequirements
    have elseTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.elseAssignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.elseAssignmentFound) shape.elseAssignmentForm elseAssignmentTyped shape.elseAssignmentType
    have branchTyped := StatementHasType.ifWithElse (lookupStatement?_sound shape.branchFound) shape.branchForm
      conditionTyped (.singleton statementTyped) (.cons initializedTyped (.singleton elseTyped)) shape.branchType
    have earlyReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.earlyReturnFound) shape.earlyReturnForm earlyTyped shape.earlyReturnType
    have earlyBranchTyped := StatementHasType.ifWithoutElse (lookupStatement?_sound shape.earlyBranchFound)
      shape.earlyBranchForm earlyConditionTyped (.singleton earlyReturnTyped) shape.earlyBranchType
    have innerReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm finalTyped shape.innerReturnType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id (.function (.product .bool .word) .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp [shape.parameterNames])
          (.cons shape.flagScheme flagExtended (.cons shape.argumentScheme argumentExtended (.nil _)))
          (.cons branchTyped (.cons earlyBranchTyped (.singleton innerReturnTyped)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Bool, Word) returns (Word)) { return lam(flag: Bool, next: Word) { if (flag) { seed = next; } else { let copy: Word = seed; seed = copy; } if (flag) { return seed; } return seed; }; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) (expected : TypeSystem.Ty) : IO (Read source binder expected) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = expected) "read raw Word"
  let ⟨type⟩ ← observed (node.type = expected) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "factory inputs")
  let [.expression condition, .expression rhs, .statement assignment, .expression initial,
      .statement initialized, .expression copy, .statement elseAssignment, .statement branch,
      .expression earlyCondition, .expression early, .statement earlyReturn, .statement earlyBranch,
      .expression final, .statement innerReturn, .expression expression, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "branch factory graph")
  let .lambda [flag, argument] _ _ := expression.form | throw (IO.userError "branch parameters")
  let .letDecl previous _ := initialized.form | throw (IO.userError "copy binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "then assignment")
  let .assignValue elseResolution .equal _ := elseAssignment.form | throw (IO.userError "else assignment")
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let earlyConditionRead ← observeRead function.typedBody flag earlyCondition .bool
  let initialRead ← observeRead function.typedBody binder initial .word
  let argumentRead ← observeRead function.typedBody argument rhs .word
  let previousRead ← observeRead function.typedBody previous copy .word
  let earlyRead ← observeRead function.typedBody binder early .word
  let finalRead ← observeRead function.typedBody binder final .word
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "branch factory flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "branch factory flagRequirements"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "branch factory flagOwner"
  let ⟨flagDistinct⟩ ← observed (flag.id ≠ binder.id) "branch factory flagDistinct"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "branch factory argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "branch factory argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "branch factory argumentOwner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "branch factory argumentDistinct"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "branch factory argumentFlag"
  let ⟨parameterNames⟩ ← observed (flag.name ≠ argument.name) "branch parameter names"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "branch factory previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "branch factory previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "branch factory previousOwner"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "branch factory previousDistinct"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "branch factory previousArgument"
  let ⟨previousFlag⟩ ← observed (previous.id ≠ flag.id) "branch factory previousFlag"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "branch factory previousOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "branch factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "branch factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function (.product .bool .word) .word]) "branch factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "branch factory inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "branch factory binderOwner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "branch factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "branch factory roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "branch factory initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initialRead.node.id)) "branch factory initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "branch factory initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "branch factory assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "branch factory assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "branch factory assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "branch factory targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "branch factory targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "branch factory targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "branch factory assignmentRequirements"
  let ⟨elseAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? elseAssignment.id = some elseAssignment) "branch factory elseAssignmentFound"
  let ⟨elseAssignmentForm⟩ ← observed (elseAssignment.form = .assignValue elseResolution .equal previousRead.node.id) "branch factory elseAssignmentForm"
  let ⟨elseAssignmentType⟩ ← observed (elseAssignment.type = .unit) "branch factory elseAssignmentType"
  let ⟨elseTargetRoot⟩ ← observed (elseResolution.target.root = binder.id) "branch factory elseTargetRoot"
  let ⟨elseTargetType⟩ ← observed (elseResolution.target.type = .word) "branch factory elseTargetType"
  let ⟨elseTargetBare⟩ ← observed (elseResolution.target.projections = []) "branch factory elseTargetBare"
  let ⟨elseAssignmentRequirements⟩ ← observed (elseResolution.requirements = []) "branch factory elseAssignmentRequirements"
  let ⟨branchFound⟩ ← observed (function.typedBody.lookupStatement? branch.id = some branch) "branch factory branchFound"
  let ⟨branchForm⟩ ← observed (branch.form = .ifThen conditionRead.node.id [assignment.id] (some [initialized.id, elseAssignment.id])) "branch factory branchForm"
  let ⟨branchType⟩ ← observed (branch.type = .unit) "branch factory branchType"
  let ⟨earlyReturnFound⟩ ← observed (function.typedBody.lookupStatement? earlyReturn.id = some earlyReturn) "branch factory earlyReturnFound"
  let ⟨earlyReturnForm⟩ ← observed (earlyReturn.form = .returnStmt (some earlyRead.node.id)) "branch factory earlyReturnForm"
  let ⟨earlyReturnType⟩ ← observed (earlyReturn.type = .word) "branch factory earlyReturnType"
  let ⟨earlyBranchFound⟩ ← observed (function.typedBody.lookupStatement? earlyBranch.id = some earlyBranch) "branch factory earlyBranchFound"
  let ⟨earlyBranchForm⟩ ← observed (earlyBranch.form = .ifThen earlyConditionRead.node.id [earlyReturn.id] none) "branch factory earlyBranchForm"
  let ⟨earlyBranchType⟩ ← observed (earlyBranch.type = .unit) "branch factory earlyBranchType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "branch factory innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some finalRead.node.id)) "branch factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "branch factory innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "branch factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "branch factory statementFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [flag, argument] .word [branch.id, earlyBranch.id, innerReturn.id]) "branch factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function (.product .bool .word) .word) "branch factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function (.product .bool .word) .word) "branch factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "branch factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "branch factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "branch factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function (.product .bool .word) .word) "branch factory statementType"
  return {binder, flag, argument, previous, conditionRead, earlyConditionRead, initialRead, argumentRead, previousRead, earlyRead, finalRead, initialized, assignment, resolution, elseAssignment, elseResolution, branch, earlyReturn, earlyBranch, innerReturn, expression, statement, flagScheme, flagRequirements, flagOwner, flagDistinct, argumentScheme, argumentRequirements, argumentOwner, argumentDistinct, argumentFlag, parameterNames, previousScheme, previousRequirements, previousOwner, previousDistinct, previousArgument, previousFlag, previousOrdinary, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, elseAssignmentFound, elseAssignmentForm, elseAssignmentType, elseTargetRoot, elseTargetType, elseTargetBare, elseAssignmentRequirements, branchFound, branchForm, branchType, earlyReturnFound, earlyReturnForm, earlyReturnType, earlyBranchFound, earlyBranchForm, earlyBranchType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, statementFound, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType}

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = sourceShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete branch factory graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected branch factory methods")
    | _, _ => throw (IO.userError "branch factory declaration count")

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchFixture
/-! Actual compilation, selected inventory and static lambda observations for
one captured Word closure with Bool/Word inputs and conditional writes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
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


structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .function (.product .bool .word) .word
  binderOrdinary : shape.binder.comptime = false
  binderScheme : shape.binder.scheme = .mono .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = shape.nodeList
  owned : shape.expression.id.occurrence.owner = row.function.typedBody.owner
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    row.function.typedBody shape.expression.id = .ok (shape.expression, reported)

abbrev ObservedFactory.binder {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.binder
abbrev ObservedFactory.flag {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.flag
abbrev ObservedFactory.flagScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.flagScheme
abbrev ObservedFactory.body {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.body
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.argumentScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme
abbrev ObservedFactory.innerReturn {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturn
abbrev ObservedFactory.expression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expression
abbrev ObservedFactory.statement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statement
abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.lambda
abbrev ObservedFactory.requirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.requirements
abbrev ObservedFactory.coercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.coercions
abbrev ObservedFactory.readForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.form
abbrev ObservedFactory.readRaw {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.raw
abbrev ObservedFactory.readType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.type
abbrev ObservedFactory.readRequirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.requirements
abbrev ObservedFactory.readCoercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.coercions
abbrev ObservedFactory.innerReturnForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnForm
abbrev ObservedFactory.innerReturnType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnType
abbrev ObservedFactory.returnStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.returnStatement
abbrev ObservedFactory.bodyRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.node
abbrev ObservedFactory.foundStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statementFound
abbrev ObservedFactory.foundExpression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expressionFound
abbrev ObservedFactory.foundRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.finalRead.found
abbrev ObservedFactory.foundInnerReturn {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnFound

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
          row.function.typedBody shape.expression.id with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (node, reported) =>
        let ⟨same⟩ ← observeFact (node = shape.expression) "packed factory reader"
        let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "packed source owner"
        let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "packed substitution"
        let ⟨closed⟩ ← observeFact (row.assumptions = []) "packed assumptions"
        let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .function (.product .bool .word) .word) "packed factory output type"
        let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "packed ordinary result"
        let ⟨binderOrdinary⟩ ← observeFact (shape.binder.comptime = false) "packed seed ordinary"
        let ⟨binderScheme⟩ ← observeFact (shape.binder.scheme = .mono .word) "packed seed type"
        let ⟨target⟩ ← observeTarget fixture row
        let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = shape.nodeList) "branch nodes"
        let ⟨owned⟩ ← observeFact (shape.expression.id.occurrence.owner = row.function.typedBody.owner) "packed lambda owner"
        let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "packed local catalog"
        let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "packed profile"
        return {
          row := row
          shape := shape
          sourceOwner := sourceOwner
          parameters := parameters
          closed := closed
          ordinary := ordinary
          resultType := resultType
          binderOrdinary := binderOrdinary
          binderScheme := binderScheme
          target := target
          nodes := nodes
          owned := owned
          noLocals := noLocals
          profile := profile
          entry := entry
          reported := reported

          member := by rw [rows]; exact .head [],
          entryMember := by rw [entries]; exact .head [],
          read := by rw [read, same]}
    | _ => throw (IO.userError "packed factory entry count")
  | _ => throw (IO.userError "packed factory specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

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


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      have same : binder = observed.binder := List.mem_singleton.mp member
      exact same ▸ observed.binderOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem ObservedFactory.lambda_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [observed.flag, observed.argument] ∧ result = .word ∧ body = observed.body := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  have alternatives : node = observed.shape.conditionRead.node ∨ node = observed.shape.argumentRead.node ∨
      node = observed.shape.initialRead.node ∨ node = observed.shape.previousRead.node ∨
      node = observed.shape.earlyConditionRead.node ∨ node = observed.shape.earlyRead.node ∨
      node = observed.shape.finalRead.node ∨ node = observed.expression := by
    simpa [FactoryShape.nodeList] using member
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [observed.shape.conditionRead.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.previousRead.form] at form; cases form
  · rw [observed.shape.earlyConditionRead.form] at form; cases form
  · rw [observed.shape.earlyRead.form] at form; cases form
  · rw [observed.shape.finalRead.form] at form; cases form
  · rw [observed.lambda] at form
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

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchMetadata
/-! The actual sixteen-node source supplies original policy metadata for all seven local reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedReadLambdaMetadata (NodeMetadata)

theorem ObservedFactory.node_metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    NodeMetadata node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.nodes] at present
  have alternatives : node = observed.shape.conditionRead.node ∨ node = observed.shape.argumentRead.node ∨ node = observed.shape.initialRead.node ∨ node = observed.shape.previousRead.node ∨ node = observed.shape.earlyConditionRead.node ∨ node = observed.shape.earlyRead.node ∨ node = observed.shape.finalRead.node ∨ node = observed.shape.expression := by
    simpa [FactoryShape.nodeList] using present
  rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨_, _, observed.shape.conditionRead.form, observed.shape.conditionRead.requirements, observed.shape.conditionRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.argumentRead.form, observed.shape.argumentRead.requirements, observed.shape.argumentRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.initialRead.form, observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.previousRead.form, observed.shape.previousRead.requirements, observed.shape.previousRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.earlyConditionRead.form, observed.shape.earlyConditionRead.requirements, observed.shape.earlyConditionRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.earlyRead.form, observed.shape.earlyRead.requirements, observed.shape.earlyRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.finalRead.form, observed.shape.finalRead.requirements, observed.shape.finalRead.coercions⟩
  · exact .inr ⟨_, _, _, observed.shape.lambda⟩

/-- Metadata follows from compiler observations, independently of a Source
trace, native execution result, caller state or a chosen body meaning. -/
theorem ObservedFactory.metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) (named : CallableIndexedNamedGeneration.Named) :
    MetadataFor fixture.recipe.compiled.indexed named observed.row.function.typedBody :=
  CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named
    (fun _ _ found => observed.node_metadata found) observed.noLocals

/-- Every authentic cached owner has the same observed original source. -/
theorem ObservedStages.metadata {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : CallableIndexedNamedGeneration.Named}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    MetadataFor fixture.recipe.compiled.indexed named (CallableIndexedNamedGeneration.source named) := by
  rw [stages.source_of_cached actual selected]
  exact observed.metadata named

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchRuntime
/-! Actual public calls retain each returned session and opaque handle.
Captures are by value: every call starts again from the seed its closure
captured, so a call's write reaches neither the next call nor another closure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithReceipt
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
          return ⟨opened.val, opened.property, fresh.val, fresh.property, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed
  executed : fixture.recipe.compiled.indexed.runSource observed.row.key [.word seed]
    runOptions.executionFuel runOptions.inputValidationFuel = .ok completion

def observeReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedReceiver fixture observed) := do
  match executed : fixture.recipe.compiled.indexed.runSource observed.row.key [.word seed]
      runOptions.executionFuel runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok completion => return ⟨completion, executed⟩


structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (flag : Bool) (argument : Core.Word) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle (.product (.bool flag) (.word argument)) runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (flag : Bool) (argument : Core.Word) : IO (ObservedInvocation session handle flag argument) := do
  let executed ← session.invokePackedWithReceipt handle (.product (.bool flag) (.word argument)) runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "packed captured call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "packed captured call exhausted")
  | .ok (.succeeded completion) => return ⟨completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "branch factory call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "branch factory call exhausted")
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "branch factory result was not a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedPublicRun fixture observed
  second : ObservedFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  distinct : first.handle ≠ second.handle
  firstCall : ObservedInvocation second.completion.session first.handle true (Core.Word.ofNatModulo 11)
  firstValue : firstCall.completion.value = .word (Core.Word.ofNatModulo 11)
  third : ObservedFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  secondCall : ObservedInvocation third.completion.session second.handle false (Core.Word.ofNatModulo 21)
  secondValue : secondCall.completion.value = .word (Core.Word.ofNatModulo 20)
  firstAgain : ObservedInvocation secondCall.completion.session first.handle false (Core.Word.ofNatModulo 12)
  finalValue : firstAgain.completion.value = .word (Core.Word.ofNatModulo 10)

private def observeWord {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact) (expected : Core.Word) :
    IO (PLift (completion.value = .word expected)) :=
  if actual : completion.value = .word expected then pure ⟨actual⟩
  else throw (IO.userError "branch returned wrong previous value")

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let second ← observeFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  let distinct ← if distinct : first.handle ≠ second.handle then pure (PLift.up distinct)
    else throw (IO.userError "distinct branch captures reused the same handle")
  let firstCall ← observeInvocation second.completion.session first.handle true (Core.Word.ofNatModulo 11)
  let ⟨firstValue⟩ ← observeWord firstCall.completion (Core.Word.ofNatModulo 11)
  let third ← observeFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  let secondCall ← observeInvocation third.completion.session second.handle false (Core.Word.ofNatModulo 21)
  let ⟨secondValue⟩ ← observeWord secondCall.completion (Core.Word.ofNatModulo 20)
  let firstAgain ← observeInvocation secondCall.completion.session first.handle false (Core.Word.ofNatModulo 12)
  let ⟨finalValue⟩ ← observeWord firstAgain.completion (Core.Word.ofNatModulo 10)
  return ⟨first, second, distinct.down, firstCall, firstValue, third, secondCall, secondValue, firstAgain, finalValue⟩

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchSyntax
/-! The original typed branch body supplies scoped arms and its restored
suffix. Only the actual read occurrences and plain captured writes are used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

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
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : WordRead source binder)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : WordRead source rhsBinder) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono .word) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = .word) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
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
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.earlyConditionRead.form,
    observed.shape.initialRead.form, observed.shape.argumentRead.form, observed.shape.previousRead.form,
    observed.shape.earlyRead.form, observed.shape.finalRead.form, observed.shape.initializedForm,
    observed.shape.assignmentForm, observed.shape.elseAssignmentForm, observed.shape.branchForm,
    observed.shape.earlyBranchForm, observed.shape.earlyReturnForm, observed.innerReturnForm,
    observed.lambda, observed.returnStatement, observed.shape.previousOwner,
    Ne.symm observed.shape.previousDistinct, Ne.symm observed.shape.previousArgument,
    Ne.symm observed.shape.previousFlag, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.earlyConditionRead.form,
    observed.shape.initialRead.form, observed.shape.argumentRead.form, observed.shape.previousRead.form,
    observed.shape.earlyRead.form, observed.shape.finalRead.form, observed.shape.initializedForm,
    observed.shape.assignmentForm, observed.shape.elseAssignmentForm, observed.shape.branchForm,
    observed.shape.earlyBranchForm, observed.shape.earlyReturnForm, observed.innerReturnForm,
    observed.lambda, observed.returnStatement, observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.shape.flagDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .conditional observed.shape.branchFound observed.shape.branchForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil)
    (.initialized observed.shape.initializedFound observed.shape.initializedForm
      (.assign observed.shape.elseAssignmentFound observed.shape.elseAssignmentForm (.inl rfl) observed.shape.elseTargetBare .nil))
    (.conditional observed.shape.earlyBranchFound observed.shape.earlyBranchForm
      (.returnValue [] observed.shape.earlyReturnFound observed.shape.earlyReturnForm) .nil
      (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm))

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.conditionRead.node.id, observed.shape.argumentRead.node.id, observed.shape.initialRead.node.id,
    observed.shape.previousRead.node.id, observed.shape.earlyConditionRead.node.id,
    observed.shape.earlyRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.branchFound first
  rw [observed.shape.branchForm] at firstForm
  cases firstForm with
  | ifWithElse conditionTyped thenTyped elseTyped =>
    apply GenericImperativeMatch.Syntax.ifThen observed.shape.branchFound observed.shape.branchForm
      (Or.inl observed.shape.branchType) observed.shape.conditionRead.found observed.shape.conditionRead.type
      (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail thenTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.argumentRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
          observed.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨boundContext, _, _, initializedHead, rest⟩ := head_tail elseTyped
      have initialized := form_at unique observed.shape.initializedFound initializedHead
      rw [observed.shape.initializedForm] at initialized
      have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
      cases initialized with
      | letInitializedGeneralized polymorphic _ _ _ _ => exact False.elim (polymorphic mono)
      | letInitialized initialTyped _ extended =>
        apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
          observed.previous_declaration mono extended
          (by simp [observed.inputs, Ne.symm observed.shape.previousDistinct])
          observed.shape.initialRead.found (by rw [observed.shape.initialRead.type, observed.shape.previousScheme]; rfl)
          (by simpa only [observed.shape.initialRead.type, observed.shape.previousScheme, TypeSystem.Scheme.mono] using initialTyped)
          (leaf _ (by simp [readIds]))
        obtain ⟨_, _, _, assignedHead, _⟩ := head_tail rest
        have assignment := form_at unique observed.shape.elseAssignmentFound assignedHead
        rw [observed.shape.elseAssignmentForm] at assignment
        cases assignment with
        | assignValue assignmentTyped =>
          exact assigned observed.shape.previousRead observed.shape.elseAssignmentFound observed.shape.elseAssignmentForm
            (by rw [observed.shape.elseTargetRoot]; exact observed.seed_declaration)
            observed.binderScheme observed.shape.elseTargetBare observed.shape.elseTargetType
            (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, early, last⟩ := head_tail tail
      have earlyForm := form_at unique observed.shape.earlyBranchFound early
      rw [observed.shape.earlyBranchForm] at earlyForm
      cases earlyForm with
      | ifWithoutElse conditionTyped thenTyped =>
        apply GenericImperativeMatch.Syntax.ifThen observed.shape.earlyBranchFound observed.shape.earlyBranchForm
          (Or.inl observed.shape.earlyBranchType) observed.shape.earlyConditionRead.found observed.shape.earlyConditionRead.type
          (by simpa only [observed.shape.earlyConditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
        · obtain ⟨_, _, _, returningHead, _⟩ := head_tail thenTyped
          exact returning unique observed.shape.earlyRead observed.shape.earlyReturnFound observed.shape.earlyReturnForm
            observed.shape.earlyReturnType (leaf _ (by simp [readIds])) returningHead
        · exact .body (.nil (.inl rfl))
        · obtain ⟨_, _, _, returningHead, _⟩ := head_tail last
          exact returning unique observed.shape.finalRead observed.shape.innerReturnFound observed.shape.innerReturnForm
            observed.shape.innerReturnType (leaf _ (by simp [readIds])) returningHead

theorem ObservedFactory.body_reads {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody)
      context (.statements true observed.shape.body) .word := by
  apply observed.body_syntax unique _ typed
  intro id member
  simp only [readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩
  · exact ⟨_, _, _, observed.shape.earlyConditionRead.found, observed.shape.earlyConditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.earlyRead.found, observed.shape.earlyRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchSupports
/-! A complete singleton inventory supplies formation and every authentic
captured-read closure body, including the actual nonempty parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
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
    observed.entryMember
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read
  · rw [actual.source]; exact observed.body_shape
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact observed.body_syntax (actual.source ▸ actual.header.unique) (fun _ _ => True.intro) typed


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedCallFaults.faults
      completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression receiver included
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩


theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor


theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Terminal header
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
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function (.product .bool .word) .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory [input] := .cons packet .nil
  have headerList : CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows = [actual.header] := by
    simp only [rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers, sameHeader]
  let stagePrepared := actualStagePrepared fixture
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.expression.id observed.statement
    observed.roots observed.foundStatement observed.returnStatement
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point receiver (fun _ _ proof => proof) (registry := registry) (faults := faults)
  let terminals : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ terminal
  have supports : ∀ header (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows),
      CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (terminals header member) faults := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, ObservedStages.registry, stagePrepared] using support
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
      apply CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic_packets
      have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
      have found := code.sourceFound
      rw [sameSource] at found
      have ⟨_parameters, resultShape, bodyShape⟩ := observed.lambda_shape found code.sourceForm
      have shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape function.source true function.body := by
        rw [sameSource, bodyShape]
        exact observed.body_shape
      have typedBody := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
        support.body.frame support.body.extended
      obtain ⟨_final, _facts, bodyTyped, _completes⟩ := typedBody
      have syntaxTree : GenericImperativeMatch.Syntax function.source
          (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read function.source)
          support.body.context (.statements true function.body) function.resultType := by
        rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
        exact observed.body_reads (sameSource ▸ support.body.unique) bodyTyped
      obtain ⟨sidecar, _issued, selected⟩ :=
        CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
      exact CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots.of_reads code support provenance receiver
        fixture.source_wellFormed (by rw [sameSource]; exact observed.metadata support.caller.named)
        shape.forget syntaxTree.prepared (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports, family := family, descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchCommon
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted nonzero-parameter factory; retained states refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
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

theorem ObservedPublicRun.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word seed] runOptions.inputValidationFuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩


theorem ObservedPublicRun.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word seed] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  have same : value = .word seed := List.mem_singleton.mp member
  exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
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
  registry : session.RegistryAt fixture.recipe.compiled.compatible.checked.staticRegistry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiver.completion.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem statement_roots_injective {left right : List StatementId}
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

private theorem returned_expression
    {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment
      before (id :: rest) finalContext (.returned value) after) :
    Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before
      expression value after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnUnit contains otherForm =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnValue contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact child.sound.value_plain
  | tail contains otherForm _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | discard contains otherForm _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letUninitialized contains otherForm _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letGeneralized contains otherForm _ _ _ _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | bitNotProjected contains otherForm _ _ _ _ _
  | bitNotBare contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem lambda_shape
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {body : List StatementId} {parameters : List TypedBinder}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ function : Dynamic.Closure,
      value = .closure function ∧ function.parameters = parameters ∧ function.resultType = .word := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw
    exact ⟨_, rfl, rfl, rfl⟩
  | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

/-- The existing public factory meaning fixes the exact returned closure,
including its original captures; no closure-shape observation is assumed. -/
theorem SourceCall.make_closure
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.actual.header invocation before [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [observed.flag, observed.argument] ∧ function.resultType = .word := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  have parameters : support.actual.header.function.parameters = [observed.shape.binder] := by
    rw [support.actual.header.parameters, ← support.actual.header.inputs,
      support.actual.source, observed.shape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, _allocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ support.actual.header.unique
  have bodyEq : support.actual.header.function.body = [observed.shape.statement.id] := by
    apply statement_roots_injective
    rw [← support.actual.header.agreement.roots, support.actual.source, observed.shape.roots]
    rfl
  have statementFound : child.source.lookupStatement? observed.shape.statement.id =
      some observed.shape.statement := by
    rw [sourceEq, support.actual.source]
    exact observed.shape.statementFound
  have expressionFound : child.source.lookupExpression? observed.shape.expression.id =
      some observed.shape.expression := by
    rw [sourceEq, support.actual.source]
    exact observed.shape.expressionFound
  rw [support.actual.result_type] at converted
  cases converted
  rw [bodyEq] at body
  exact lambda_shape unique expressionFound observed.shape.lambda observed.shape.coercions
    (returned_expression unique statementFound observed.shape.returnStatement body)

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchInvocation
/-! Actual Bool/Word public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (flag : Bool) (argument : Core.Word) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [.bool flag, .word argument] outcome after

/-- Both the packed argument and callee meaning come from the original encoder
and current History. The returned state uses this call's exact public completion. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function (.product .bool .word) .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    (parameters : function.parameters = [observed.flag, observed.argument])
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.product .bool .word) .word)
    {flag : Bool} {argument : Core.Word} (call : ObservedInvocation publicSession handle flag argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source flag argument (.value (.word word)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context (.product .bool .word)
      (.product (.bool flag) (.word argument)) (.product (.bool flag) (.word argument)) :=
    .product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
        ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩)
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, started, _parameterView, _resultView, succeeded,
      actualAt, packing, arity, trace, result, _related, retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectPackedPublicHistory.public_invoke_succeeded_function_tree
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.product (.bool flag) (.word argument)))
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function (.product .bool .word) .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [.bool flag, .word argument] :=
    packing.injective_of_length_eq (.cons (.singleton (.word argument))) (by simpa [parameters] using arity)
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, sourcesEq, outcomeValue] using trace

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedFactory fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function (.product .bool .word) .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function (.product .bool .word) .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.actual.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.actual.header := by
    have member := (congrArg (fun items => request.header ∈ items) support.header_list).mp request.selected.member
    exact List.mem_singleton.mp member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.actual.input_types]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.descriptor
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact receiver.completion.result.extension)
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
  rw [resultType, selected, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function (.product .bool .word) .word
    rw [selected]
    exact support.actual.result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed)
    (first : ObservedPublicRun fixture observed) :
    ∃ entry : Entry,
      entry.sourceType = .function (.product .bool .word) .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function (.product .bool .word) .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.actual.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    first.start_receipt
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry :=
    first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.started first.executed first.returned support.descriptor
  let entry : Entry := ⟨support.actual.header.function.resultType, source, first.handle,
    payload, support.actual.header.output, runOptions.outputValidationFuel⟩
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
    registry := returnedRegistry
    history := retained }
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.actual.result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.input.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩


end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchPublicExecution
/-! The first closure is called again after a separate closure and a fresh
factory allocation, and its second call starts again from its captured seed:
the write of its first call does not carry over. Every transition uses the
actual returned public session and the same Source heap retained by the
previous call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function (.product .bool .word) .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function (.product .bool .word) .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function (.product .bool .word) .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.flag, observed.argument] ∧ secondClosure.parameters = [observed.flag, observed.argument] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source true (Core.Word.ofNatModulo 11)
          (.value (.word (Core.Word.ofNatModulo 11))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source false (Core.Word.ofNatModulo 21)
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source false (Core.Word.ofNatModulo 12)
          (.value (.word (Core.Word.ofNatModulo 10))) final.heap

/-- Accepted checker/compiler observations construct all static support. The
last returned ten is the first handle's captured seed, not its first call's
write. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed stages receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨firstEntry, firstType, firstHandle, firstHandleType, first, firstTrace⟩ :=
    first_meaning support stages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨secondEntry, secondType, secondHandle, secondHandleType, second, secondTrace⟩ :=
    first.make_typed_handle sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨written, writtenTrace⟩ := invoke second firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstCall sequence.firstValue scope
  obtain ⟨thirdEntry, thirdType, thirdHandle, _thirdHandleType, third, thirdTrace⟩ :=
    written.make_typed_handle sequence.third scope
  obtain ⟨other, otherTrace⟩ := invoke third secondEntry (by simp) secondType secondSource
    secondParameters secondHandle secondHandleType sequence.secondCall sequence.secondValue scope
  obtain ⟨final, finalTrace⟩ := invoke other firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstAgain sequence.finalValue scope
  have distinct : firstEntry.handle ≠ secondEntry.handle := by
    rw [firstHandle, secondHandle]
    exact sequence.distinct
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed stages sequence receiver
  IO.println "Actual captured branches: make10/make20, first(true,11) returns11, make30, second(false,21) returns20, first(false,12) returns10; six Source calls and returned histories proved"

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedBranchForward
/-! The actual conditional calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (flag : Bool) (argument word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.product (.bool flag) (.word argument)) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function (.product .bool .word) .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {flag : Bool} {argument word : Core.Word} (call : ObservedInvocation publicSession handle flag argument)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source flag argument (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle flag argument word after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have registryEq := started.function_tree_registry (.simple (.product (.bool flag) (.word argument))) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context (.product .bool .word)
      (.product (.bool flag) (.word argument)) (.product (.bool flag) (.word argument)) :=
    .product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
        ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩)
  obtain ⟨size, trace⟩ := trace
  rw [entrySource] at trace
  rw [← entryHandle] at started
  obtain ⟨required, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectWordPreservation.public_resume_has_sufficient_fuel
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) started metadata (.cons (.singleton (.word argument))) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function (.product .bool .word) .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function (.product .bool .word) .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function (.product .bool .word) .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.flag, observed.argument] ∧ secondClosure.parameters = [observed.flag, observed.argument] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source true (Core.Word.ofNatModulo 11)
          (.value (.word (Core.Word.ofNatModulo 11))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source false (Core.Word.ofNatModulo 21)
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source false (Core.Word.ofNatModulo 12)
          (.value (.word (Core.Word.ofNatModulo 10))) final.heap ∧
        ForwardWordAt support sequence.second.completion.session [firstEntry, secondEntry] sequence.first.handle
          true (Core.Word.ofNatModulo 11) (Core.Word.ofNatModulo 11) written.heap ∧
        ForwardWordAt support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry] sequence.second.handle
          false (Core.Word.ofNatModulo 21) (Core.Word.ofNatModulo 20) other.heap ∧
        ForwardWordAt support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry] sequence.first.handle
          false (Core.Word.ofNatModulo 12) (Core.Word.ofNatModulo 10) final.heap

/-- Both chosen branch arms and the early-return path have a forward public
fuel guarantee on their original checkpoints, with exact Source post-heaps. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed)
    (receiver : ObservedReceiver fixture observed) : ForwardMeaning stages sequence receiver := by
  obtain ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
      firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
      firstSource, secondSource, firstParameters, secondParameters,
      first, second, written, third, other, final,
      firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩ :=
    sequence_meaning fixture observed stages sequence receiver
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace,
    forward_word second firstEntry (by simp) firstType firstSource firstHandle sequence.firstCall writtenTrace,
    forward_word third secondEntry (by simp) secondType secondSource secondHandle sequence.secondCall otherTrace,
    forward_word other firstEntry (by simp) firstType firstSource firstHandle sequence.firstAgain finalTrace⟩

/-- The observed scenario is shared by reflection and forward preservation. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed stages sequence receiver
  IO.println "Actual captured branches: independent Source traces, returned histories and sufficient public Word export fuel proved for all three direct calls"

end Tests.SourceCoreCapturedBranch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchSource
/-! Independent Source typing for a closure that returns its previous captured
Word and writes its argument into the same captured cell. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics

structure WordRead (source : TypedSource) (binder : TypedBinder) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .reference binder.name (.local binder.id)
  raw : node.rawType = .word
  type : node.type = .word
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem WordRead.typed {source : TypedSource} {binder : TypedBinder}
    (read : WordRead source binder) {context : SourceSemantics.Context}
    (scheme : binder.scheme = .mono .word) (requirements : binder.schemeRequirements = [])
    (word : TypeAdmissible context .word)
    (lookup : context.LocalLookup binder.id binder.scheme)
    (localRequirements : context.LocalSchemeRequirementsLookup binder.id binder.schemeRequirements) :
    ExpressionHasType source context read.node.id .word := by
  have instantiated : LocalSchemeInstantiationValid context binder .word [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ requirements)
      (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, requirements]
      exact .nil
  rw [← read.type]
  refine .intro (lookupExpression?_sound read.found)
    (read.form ▸ ExpressionFormHasRawType.reference (.local lookup localRequirements instantiated))
    read.raw word (read.type ▸ word) ?_
  rw [read.requirements, read.coercions, read.type]
  exact .ordinary (by intro id member; cases member) (.nil _) rfl

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  argument : TypedBinder
  previous : TypedBinder
  copyBinder : TypedBinder
  matchNode : StatementNode
  matching : MatchResolution
  arm : TypedMatchCase
  patternSpan : Syntax.SourceSpan
  owner : function.typedBody.owner = signature.id
  localScheme : copyBinder.scheme = .mono .word
  localRequirements : copyBinder.schemeRequirements = []
  localOrdinary : copyBinder.comptime = false
  localOwner : copyBinder.id.owner = function.typedBody.owner
  localSeed : copyBinder.id ≠ binder.id
  localArgument : copyBinder.id ≠ argument.id
  localPrevious : copyBinder.id ≠ previous.id
  hiddenSeed : matching.hiddenScrutinee ≠ binder.id
  hiddenArgument : matching.hiddenScrutinee ≠ argument.id
  hiddenPrevious : matching.hiddenScrutinee ≠ previous.id
  localHidden : copyBinder.id ≠ matching.hiddenScrutinee
  arms : matching.cases = [arm]
  noDefault : matching.defaultBody = none
  matchRequirements : matching.requirements = []
  patternSource : arm.pattern.source = .binder patternSpan copyBinder.name
  patternResolution : arm.pattern.resolution = .binder copyBinder
  patternType : arm.pattern.type = .word
  patternRequirements : arm.pattern.requirements = []
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentDistinct : argument.id ≠ binder.id
  previousScheme : previous.scheme = .mono .word
  previousRequirements : previous.schemeRequirements = []
  previousOwner : previous.id.owner = function.typedBody.owner
  previousDistinct : previous.id ≠ binder.id
  previousArgument : previous.id ≠ argument.id
  previousOrdinary : previous.comptime = false
  initialRead : WordRead function.typedBody binder
  argumentRead : WordRead function.typedBody argument
  localRead : WordRead function.typedBody copyBinder
  scrutinee : matching.scrutinee = argumentRead.node.id
  previousRead : WordRead function.typedBody previous
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  armBody : arm.body = [assignment.id]
  matchFound : function.typedBody.lookupStatement? matchNode.id = some matchNode
  matchForm : matchNode.form = .matchWith matching
  matchType : matchNode.type = .unit
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .word .word]
  inputs : function.typedBody.inputs = [binder]
  binderOwner : binder.id.owner = function.typedBody.owner
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl previous (some initialRead.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal localRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  innerReturnForm : innerReturn.form = .returnStmt (some previousRead.node.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [argument] .word [initialized.id, matchNode.id, innerReturn.id]
  expressionRaw : expression.rawType = .function .word .word
  expressionType : expression.type = .function .word .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .word .word

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

theorem FactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := { type := .function .word .word, hasValue := true, sawReturn := true, control := .returned }
  let ordinary : StatementFacts := { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }
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
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical (.function .word .word) := ⟨binders, .function (.builtin .word) (.builtin .word)⟩
    let arguments := lexical.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner lexical shape.argument arguments := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible word
          quantified_fresh := by rw [shape.argumentScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.argumentRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.argumentDistinct]
    have argumentWord : TypeAdmissible arguments .word := ⟨binders, .builtin .word⟩
    let locals := arguments.withLocal shape.previous.id shape.previous.scheme shape.previous.schemeRequirements
    have previousExtended : BinderExtends function.typedBody.owner arguments shape.previous locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.previousOwner
          scheme := shape.previousScheme.symm ▸ SchemeWellFormed.monoAdmissible argumentWord
          quantified_fresh := by rw [shape.previousScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.previousRequirements }
      · cases head
        simp [arguments, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.previousDistinct, shape.previousArgument]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have initialTyped := shape.initialRead.typed scheme shape.binderRequirements argumentWord
      (.tail shape.argumentDistinct head.local_self) (.tail shape.argumentDistinct head.local_scheme_requirements_self)
    have rhsTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements localWord
      (.tail shape.previousArgument argumentExtended.local_self)
      (.tail shape.previousArgument argumentExtended.local_scheme_requirements_self)
    have previousTyped := shape.previousRead.typed shape.previousScheme shape.previousRequirements localWord
      previousExtended.local_self previousExtended.local_scheme_requirements_self
    have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ arguments shape.initialized.id locals ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.previousScheme, TypeSystem.Scheme.mono] using initialTyped
      · rw [shape.previousScheme]; rfl
      · rw [shape.previousScheme]; rfl
      · exact previousExtended
      · exact shape.initializedType
    let armContext := locals.withLocal shape.copyBinder.id shape.copyBinder.scheme shape.copyBinder.schemeRequirements
    have copyExtended : BinderExtends function.typedBody.owner locals shape.copyBinder armContext := by
      apply BinderExtends.intro
      · exact { owned := shape.localOwner
                scheme := shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible localWord
                quantified_fresh := by rw [shape.localScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                monomorphic_requirements_empty := fun _ => shape.localRequirements }
      · cases head
        simp [locals, arguments, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.localSeed, shape.localArgument, shape.localPrevious]
    have armWord : TypeAdmissible armContext .word := ⟨binders, .builtin .word⟩
    have localTyped := shape.localRead.typed shape.localScheme shape.localRequirements armWord
      copyExtended.local_self copyExtended.local_scheme_requirements_self
    have writable : WritableLocal armContext shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro (.tail shape.localSeed (.tail shape.previousDistinct (.tail shape.argumentDistinct head.local_self)))
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible armWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody armContext shape.resolution .equal shape.localRead.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) localTyped shape.assignmentRequirements
    have assigned : StatementHasType function.typedBody ⟨.word, 0⟩ armContext shape.assignment.id armContext ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have patternSource : MatchPatternSourceRepresents locals shape.arm.pattern.source shape.arm.pattern.resolution 0 := by
      rw [shape.patternSource, shape.patternResolution]
      exact .binder rfl
    have patternBinder : PatternBinderValid locals .word shape.copyBinder := {
      scheme_eq := shape.localScheme
      runtime := shape.localOrdinary
      wellFormed := by
        intro declaration current
        have same : declaration = function.typedBody.owner := by
          change lexical.currentDeclaration = some declaration at current
          rw [head.context_fields.2.1] at current
          have owner : signature.id = declaration := Option.some.inj current
          exact owner.symm.trans shape.owner.symm
        rw [same]
        cases copyExtended with
        | intro wellFormed _ => exact wellFormed }
    have patternTyped : TypedMatchPatternHasType locals shape.arm.pattern .word [shape.copyBinder] 0 := {
      type_eq := shape.patternType
      source_represents := patternSource
      resolution_type := by
        rw [shape.patternResolution, shape.patternRequirements]
        exact .binder patternBinder
      binders_distinct := ⟨by simp, by simp⟩ }
    have armTyped : MatchCaseHasType function.typedBody ⟨.word, 0⟩ locals .word
        shape.arm (BodyFacts.singleton ordinary) :=
      .intro patternTyped (.cons copyExtended (.nil _))
        (shape.armBody.symm ▸ StatementsHaveType.singleton assigned)
    have statementTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.matchNode.id locals ordinary := by
      apply StatementHasType.matchWithoutDefault
        (caseFacts := [BodyFacts.singleton ordinary]) (summary := .ordinary .unit)
        (lookupStatement?_sound shape.matchFound) shape.matchForm shape.noDefault
      · rw [shape.scrutinee]; exact rhsTyped
      · rw [shape.arms]; exact .cons armTyped (.nil _ _ _)
      · rw [shape.matchRequirements, shape.arms]; simp [shape.patternRequirements]
      · rw [shape.arms]
        apply MatchExhaustive.catchall (matchCase := shape.arm) (.head _)
        refine ⟨0, patternSource, ?_⟩
        rw [shape.patternResolution]
        exact .binder
      · rfl
      · exact shape.matchType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id (.function .word .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp)
          (.cons shape.argumentScheme argumentExtended (.nil _))
          (.cons initializedTyped (.cons statementTyped (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm previousTyped shape.innerReturnType))))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(next: Word) { let previous: Word = seed; match (next) { case copy { seed = copy; } } return previous; }; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) : IO (WordRead source binder) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = .word) "read raw Word"
  let ⟨type⟩ ← observed (node.type = .word) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "factory inputs")
  let [.expression initial, .statement initialized, .expression scrutineeNode, .expression rhs, .statement assignment, .statement matchNode,
      .expression old, .statement innerReturn, .expression expression, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "match factory graph")
  let .lambda [argument] _ _ := expression.form | throw (IO.userError "lambda argument")
  let .letDecl previous _ := initialized.form | throw (IO.userError "previous binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare assignment")
  let .matchWith matching := matchNode.form | throw (IO.userError "match node")
  let [arm] := matching.cases | throw (IO.userError "match arm")
  let .binder copyBinder := arm.pattern.resolution | throw (IO.userError "pattern binder")
  let .binder patternSpan _ := arm.pattern.source | throw (IO.userError "pattern source")
  let initialRead ← observeRead function.typedBody binder initial
  let argumentRead ← observeRead function.typedBody argument scrutineeNode
  let localRead ← observeRead function.typedBody copyBinder rhs
  let previousRead ← observeRead function.typedBody previous old
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "match factory argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "match factory argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "match factory argumentOwner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "match factory argumentDistinct"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "match factory previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "match factory previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "match factory previousOwner"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "match factory previousDistinct"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "match factory previousArgument"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "match factory previousOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "match factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "match factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .word .word]) "match factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "match factory inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "match factory binder owner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "match factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "match factory roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "match factory initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initialRead.node.id)) "match factory initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "match factory initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "match factory assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal localRead.node.id) "match factory assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "match factory assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "match factory targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "match factory targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "match factory targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "match factory assignmentRequirements"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "match factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "match factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "match factory statementFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some previousRead.node.id)) "match factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "match factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [argument] .word [initialized.id, matchNode.id, innerReturn.id]) "match factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .word .word) "match factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .word .word) "match factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "match factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "match factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "match factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .word .word) "match factory statementType"
  let ⟨owner⟩ ← observed (function.typedBody.owner = signature.id) "match factory owner"
  let ⟨localScheme⟩ ← observed (copyBinder.scheme = .mono .word) "match factory localScheme"
  let ⟨localRequirements⟩ ← observed (copyBinder.schemeRequirements = []) "match factory localRequirements"
  let ⟨localOrdinary⟩ ← observed (copyBinder.comptime = false) "match factory localOrdinary"
  let ⟨localOwner⟩ ← observed (copyBinder.id.owner = function.typedBody.owner) "match factory localOwner"
  let ⟨localSeed⟩ ← observed (copyBinder.id ≠ binder.id) "match factory localSeed"
  let ⟨localArgument⟩ ← observed (copyBinder.id ≠ argument.id) "match factory localArgument"
  let ⟨localPrevious⟩ ← observed (copyBinder.id ≠ previous.id) "match factory localPrevious"
  let ⟨hiddenSeed⟩ ← observed (matching.hiddenScrutinee ≠ binder.id) "match factory hiddenSeed"
  let ⟨hiddenArgument⟩ ← observed (matching.hiddenScrutinee ≠ argument.id) "match factory hiddenArgument"
  let ⟨hiddenPrevious⟩ ← observed (matching.hiddenScrutinee ≠ previous.id) "match factory hiddenPrevious"
  let ⟨localHidden⟩ ← observed (copyBinder.id ≠ matching.hiddenScrutinee) "match factory localHidden"
  let ⟨arms⟩ ← observed (matching.cases = [arm]) "match factory arms"
  let ⟨noDefault⟩ ← observed (matching.defaultBody = none) "match factory noDefault"
  let ⟨matchRequirements⟩ ← observed (matching.requirements = []) "match factory matchRequirements"
  let ⟨patternSource⟩ ← observed (arm.pattern.source = .binder patternSpan copyBinder.name) "match factory patternSource"
  let ⟨patternResolution⟩ ← observed (arm.pattern.resolution = .binder copyBinder) "match factory patternResolution"
  let ⟨patternType⟩ ← observed (arm.pattern.type = .word) "match factory patternType"
  let ⟨patternRequirements⟩ ← observed (arm.pattern.requirements = []) "match factory patternRequirements"
  let ⟨scrutinee⟩ ← observed (matching.scrutinee = argumentRead.node.id) "match factory scrutinee"
  let ⟨armBody⟩ ← observed (arm.body = [assignment.id]) "match factory armBody"
  let ⟨matchFound⟩ ← observed (function.typedBody.lookupStatement? matchNode.id = some matchNode) "match factory matchFound"
  let ⟨matchForm⟩ ← observed (matchNode.form = .matchWith matching) "match factory matchForm"
  let ⟨matchType⟩ ← observed (matchNode.type = .unit) "match factory matchType"
  return { copyBinder, matchNode, matching, arm, patternSpan, localRead, owner, localScheme, localRequirements, localOrdinary, localOwner, localSeed, localArgument, localPrevious, hiddenSeed, hiddenArgument, hiddenPrevious, localHidden, arms, noDefault, matchRequirements, patternSource, patternResolution, patternType, patternRequirements, scrutinee, armBody, matchFound, matchForm, matchType, binder, argument, previous, initialRead, argumentRead, previousRead, initialized, assignment, resolution, innerReturn, expression, statement, argumentScheme, argumentRequirements, argumentOwner, argumentDistinct, previousScheme, previousRequirements, previousOwner, previousDistinct, previousArgument, previousOrdinary, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, innerReturnFound, expressionFound, statementFound, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : FactoryShape function signature
  nodes : function.typedBody.nodes = [.expression sourceShape.initialRead.node, .statement sourceShape.initialized,
    .expression sourceShape.argumentRead.node, .expression sourceShape.localRead.node, .statement sourceShape.assignment, .statement sourceShape.matchNode,
    .expression sourceShape.previousRead.node, .statement sourceShape.innerReturn,
    .expression sourceShape.expression, .statement sourceShape.statement]

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← observeShape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = [.expression sourceShape.initialRead.node, .statement sourceShape.initialized,
          .expression sourceShape.argumentRead.node, .expression sourceShape.localRead.node, .statement sourceShape.assignment, .statement sourceShape.matchNode,
          .expression sourceShape.previousRead.node, .statement sourceShape.innerReturn,
          .expression sourceShape.expression, .statement sourceShape.statement]) "complete match factory graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected match factory methods")
    | _, _ => throw (IO.userError "match factory declaration count")

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchFixture
/-! Actual compilation, selected inventory and static lambda observations for
one mutable captured Word closure with one Word argument. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics

private def observeFact (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

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
  let signature :: _ := checked.program.signatures.functions
    | throw (IO.userError "factory signature missing")
  let seeds := [SourceCompiler.Seed.declaration signature.id]
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


structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .function .word .word
  binderOrdinary : shape.binder.comptime = false
  binderScheme : shape.binder.scheme = .mono .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = [.expression shape.initialRead.node, .statement shape.initialized,
    .expression shape.argumentRead.node, .expression shape.localRead.node, .statement shape.assignment, .statement shape.matchNode,
    .expression shape.previousRead.node, .statement shape.innerReturn,
    .expression shape.expression, .statement shape.statement]
  owned : shape.expression.id.occurrence.owner = row.function.typedBody.owner
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    row.function.typedBody shape.expression.id = .ok (shape.expression, reported)

abbrev ObservedFactory.binder {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.binder
abbrev ObservedFactory.argument {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argument
abbrev ObservedFactory.argumentScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.argumentScheme
abbrev ObservedFactory.innerReturn {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturn
abbrev ObservedFactory.expression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expression
abbrev ObservedFactory.statement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statement
abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.lambda
abbrev ObservedFactory.requirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.requirements
abbrev ObservedFactory.coercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.coercions
abbrev ObservedFactory.readForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.form
abbrev ObservedFactory.readRaw {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.raw
abbrev ObservedFactory.readType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.type
abbrev ObservedFactory.readRequirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.requirements
abbrev ObservedFactory.readCoercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.coercions
abbrev ObservedFactory.innerReturnForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnForm
abbrev ObservedFactory.innerReturnType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnType
abbrev ObservedFactory.returnStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.returnStatement
abbrev ObservedFactory.bodyRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.node
abbrev ObservedFactory.foundStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statementFound
abbrev ObservedFactory.foundExpression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expressionFound
abbrev ObservedFactory.foundRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.previousRead.found
abbrev ObservedFactory.foundInnerReturn {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnFound

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observeFact (key = row.key) "captured factory exact key"
    return ⟨by rw [accepted, same]⟩

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    let shape ← observeShape row.function fixture.signature
    match entries : fixture.recipe.compiled.indexed.entries with
    | [entry] =>
      match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
          row.function.typedBody shape.expression.id with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (node, reported) =>
        let ⟨same⟩ ← observeFact (node = shape.expression) "packed factory reader"
        let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "packed source owner"
        let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "packed substitution"
        let ⟨closed⟩ ← observeFact (row.assumptions = []) "packed assumptions"
        let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .function .word .word) "packed factory output type"
        let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "packed ordinary result"
        let ⟨binderOrdinary⟩ ← observeFact (shape.binder.comptime = false) "packed seed ordinary"
        let ⟨binderScheme⟩ ← observeFact (shape.binder.scheme = .mono .word) "packed seed type"
        let ⟨target⟩ ← observeTarget fixture row
        let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = [.expression shape.initialRead.node, .statement shape.initialized,
          .expression shape.argumentRead.node, .expression shape.localRead.node, .statement shape.assignment, .statement shape.matchNode,
          .expression shape.previousRead.node, .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]) "packed nodes"
        let ⟨owned⟩ ← observeFact (shape.expression.id.occurrence.owner = row.function.typedBody.owner) "packed lambda owner"
        let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "packed local catalog"
        let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "packed profile"
        return {
          row := row
          shape := shape
          sourceOwner := sourceOwner
          parameters := parameters
          closed := closed
          ordinary := ordinary
          resultType := resultType
          binderOrdinary := binderOrdinary
          binderScheme := binderScheme
          target := target
          nodes := nodes
          owned := owned
          noLocals := noLocals
          profile := profile
          entry := entry
          reported := reported

          member := by rw [rows]; exact .head [],
          entryMember := by rw [entries]; exact .head [],
          read := by rw [read, same]}
    | _ => throw (IO.userError "packed factory entry count")
  | _ => throw (IO.userError "packed factory specialization count")

/-- The staged selection is obtained from the retained callable table and
original sidecar of the concrete compiler result. -/
structure ObservedStages (fixture : CompiledFixture)
    (observed : ObservedFactory fixture) where
  singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      if singletonGlobal : fixture.recipe.compiled.indexed.base.globals.length = 1 then
        match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
            (.named observed.row.key) with
        | .error error => throw (IO.userError (reprStr error))
        | .ok descriptor => return ⟨singletonGlobal, descriptor, native, present, sidecar, issued⟩
      else throw (IO.userError "factory global count")

def ObservedStages.registry {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem ActualHeader.complete {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [actual.header] := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled actual.prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : actual.prepared.index = 0 := by omega
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [stages.singletonGlobal] at bound
  have indexZero : index = 0 := by omega
  refine ⟨actual.header, .head [], actual.aligned.slot.trans (zero.trans indexZero.symm), ?_⟩
  rw [actual.aligned.named]
  rw [zero] at selected
  rw [indexZero] at found
  exact Option.some.inj (selected.symm.trans found)

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


theorem ObservedStages.inventory {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row, actual.header = packet.header := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  have target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation observed.row) = .ok prepared.named.signature.key := by
    rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
    exact observed.target
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [stages.singletonGlobal] at bound
  have zero : prepared.index = 0 := by omega
  have globals : fixture.recipe.compiled.indexed.base.globals = [prepared.named.signature] := by
    obtain ⟨first, single⟩ := List.length_eq_one_iff.mp stages.singletonGlobal
    rw [single, zero] at selected
    have same : first = prepared.named.signature := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
    exact single.trans (congrArg (fun value => [value]) same)
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := by
      intro binder member
      rw [observed.inputs] at member
      have same : binder = observed.binder := List.mem_singleton.mp member
      exact same ▸ observed.binderOrdinary
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl⟩



theorem ObservedStages.source_of_cached {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 1 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using stages.singletonGlobal
  have before := (List.getElem?_eq_some_iff.mp actual.prepared.selected).1
  have after := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at before after
  have same : index = actual.prepared.index := by omega
  rw [same, actual.prepared.selected] at selected
  cases Option.some.inj selected
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem ObservedFactory.lambda_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [observed.argument] ∧ result = .word ∧
      body = [observed.shape.initialized.id, observed.shape.matchNode.id, observed.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  have alternatives : node = observed.shape.initialRead.node ∨ node = observed.shape.argumentRead.node ∨
      node = observed.shape.localRead.node ∨ node = observed.shape.previousRead.node ∨ node = observed.expression := by simpa using member
  rcases alternatives with rfl | rfl | rfl | rfl | rfl
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
  · rw [observed.shape.localRead.form] at form; cases form
  · rw [observed.shape.previousRead.form] at form; cases form
  · rw [observed.lambda] at form
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

theorem CompiledFixture.signature_member (fixture : CompiledFixture) :
    fixture.signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
  rw [fixture.sameProgram, fixture.signatures]
  exact .head []

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same


end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchMetadata
/-! The actual ten-node source supplies original policy metadata for all four original local reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedReadLambdaMetadata (NodeMetadata)

theorem ObservedFactory.node_metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    NodeMetadata node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.nodes] at present
  have alternatives : node = observed.shape.initialRead.node ∨ node = observed.shape.argumentRead.node ∨
      node = observed.shape.localRead.node ∨ node = observed.shape.previousRead.node ∨ node = observed.shape.expression := by simpa using present
  rcases alternatives with rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨_, _, observed.shape.initialRead.form,
      observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.argumentRead.form,
      observed.shape.argumentRead.requirements, observed.shape.argumentRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.localRead.form,
      observed.shape.localRead.requirements, observed.shape.localRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.previousRead.form,
      observed.shape.previousRead.requirements, observed.shape.previousRead.coercions⟩
  · exact .inr ⟨_, _, _, observed.shape.lambda⟩

/-- Metadata follows from compiler observations, independently of a Source
trace, native execution result, caller state or a chosen body meaning. -/
theorem ObservedFactory.metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) (named : CallableIndexedNamedGeneration.Named) :
    MetadataFor fixture.recipe.compiled.indexed named observed.row.function.typedBody :=
  CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named
    (fun _ _ found => observed.node_metadata found) observed.noLocals

/-- Every authentic cached owner has the same observed original source. -/
theorem ObservedStages.metadata {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {index : Nat} {named : CallableIndexedNamedGeneration.Named}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    MetadataFor fixture.recipe.compiled.indexed named (CallableIndexedNamedGeneration.source named) := by
  rw [stages.source_of_cached actual selected]
  exact observed.metadata named

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchRuntime
/-! Actual public calls retain each returned session and opaque handle.
Captures are by value: every call starts again from the seed its closure
captured, so a call's write reaches neither the next call nor another closure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observePublicRun (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithReceipt
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
          return ⟨opened.val, opened.property, fresh.val, fresh.property, session, ready,
            checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
        | _ => throw (IO.userError "factory output was not a function handle")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : Core.Word) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle (.word argument) runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : Core.Word) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (.word argument) runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "packed captured call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "packed captured call exhausted")
  | .ok (.succeeded completion) => return ⟨completion, result ▸ executed.property⟩

structure ObservedFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeFunctionCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceSpecialization.SpecializationKey)
    (arguments : List SourceCorePublicValues.Value) : IO (ObservedFunctionCall session key arguments) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "match factory call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "match factory call exhausted")
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "match factory result was not a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedPublicRun fixture observed
  second : ObservedFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  distinct : first.handle ≠ second.handle
  firstCall : ObservedInvocation second.completion.session first.handle (Core.Word.ofNatModulo 11)
  firstValue : firstCall.completion.value = .word (Core.Word.ofNatModulo 10)
  third : ObservedFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  secondCall : ObservedInvocation third.completion.session second.handle (Core.Word.ofNatModulo 21)
  secondValue : secondCall.completion.value = .word (Core.Word.ofNatModulo 20)
  firstAgain : ObservedInvocation secondCall.completion.session first.handle (Core.Word.ofNatModulo 12)
  finalValue : firstAgain.completion.value = .word (Core.Word.ofNatModulo 10)

private def observeWord {artifact : SourceCoreExecution.Artifact}
    (completion : SourceCoreExecution.Completion artifact) (expected : Core.Word) :
    IO (PLift (completion.value = .word expected)) :=
  if actual : completion.value = .word expected then pure ⟨actual⟩
  else throw (IO.userError "match returned wrong previous value")

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let second ← observeFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  let distinct ← if distinct : first.handle ≠ second.handle then pure (PLift.up distinct)
    else throw (IO.userError "distinct match captures reused the same handle")
  let firstCall ← observeInvocation second.completion.session first.handle (Core.Word.ofNatModulo 11)
  let ⟨firstValue⟩ ← observeWord firstCall.completion (Core.Word.ofNatModulo 10)
  let third ← observeFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  let secondCall ← observeInvocation third.completion.session second.handle (Core.Word.ofNatModulo 21)
  let ⟨secondValue⟩ ← observeWord secondCall.completion (Core.Word.ofNatModulo 20)
  let firstAgain ← observeInvocation secondCall.completion.session first.handle (Core.Word.ofNatModulo 12)
  let ⟨finalValue⟩ ← observeWord firstAgain.completion (Core.Word.ofNatModulo 10)
  return ⟨first, second, distinct.down, firstCall, firstValue, third, secondCall, secondValue, firstAgain, finalValue⟩

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchSyntax
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : WordRead source binder)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : WordRead source rhsBinder) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono .word) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = .word) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
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
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.localRead.form, observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, List.filter_nil,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.previousOwner, Ne.symm observed.shape.previousDistinct,
    Ne.symm observed.shape.previousArgument, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements, observed.shape.localPrevious]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.localRead.form, observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, List.filter_nil,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements, observed.shape.localSeed]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape observed.row.function.typedBody true
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] := by
  apply CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape.initialized
    observed.shape.initializedFound observed.shape.initializedForm
  apply CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape.matchWith observed.shape.matchFound observed.shape.matchForm
  · intro arm member
    have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
    subst arm
    rw [observed.shape.armBody]
    exact .assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil
  · intro statements present
    simp [observed.shape.noDefault] at present
  · exact .returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm

private theorem binders_functional {owner : Resolved.DeclarationId}
    {context left right : SourceSemantics.Context} {binders : List TypedBinder}
    (first : BindersExtend owner context binders left) (second : BindersExtend owner context binders right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => cases head; cases other; exact ih rest

private theorem requested_body {source : TypedSource} {control : ControlContext}
    {parent child : SourceSemantics.Context} {type : TypeSystem.Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (typed : MatchCasesHaveType source control parent type cases caseFacts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final facts, StatementsHaveType source control parent statements final facts)
    (selected : GenericMatchChildren.ContextFor source parent type cases fallback request child) :
    ∃ final facts, StatementsHaveType source control child request.statements final facts := by
  cases selected with
  | @arm arm binders arity child member statements patternTyped extended =>
    have caseTyped : ∃ facts, MatchCaseHasType source control parent type arm facts := by
      induction cases generalizing caseFacts with
      | nil => cases member
      | cons head rest ih =>
        cases typed with
        | cons headTyped tail =>
          rcases List.mem_cons.mp member with same | later
          · subst arm; exact ⟨_, headTyped⟩
          · exact ih tail later
    obtain ⟨facts, caseTyped⟩ := caseTyped
    cases caseTyped with
    | intro originalPattern originalExtension body =>
      have bindersEq := (CompatiblePatternSourceBinders.pattern_binders originalPattern).symm.trans
        (CompatiblePatternSourceBinders.pattern_binders patternTyped)
      cases bindersEq
      have same := binders_functional originalExtension extended
      rw [← same, statements]
      exact ⟨_, _, body⟩
  | default present => exact defaultTyped _ present

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.argumentRead.node.id,
    observed.shape.localRead.node.id, observed.shape.previousRead.node.id]

private theorem tail_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.matchFound first
  rw [observed.shape.matchForm] at firstForm
  cases firstForm with
  | matchWithDefault present _ _ _ => simp [observed.shape.noDefault] at present
  | matchWithoutDefault absent scrutineeTyped casesTyped =>
    have scrutineeFound : observed.row.function.typedBody.lookupExpression? observed.shape.matching.scrutinee =
        some observed.shape.argumentRead.node := by rw [observed.shape.scrutinee]; exact observed.shape.argumentRead.found
    obtain ⟨stored, contained, storedType⟩ := scrutineeTyped.stored_type
    have same := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans scrutineeFound)
    subst stored
    have defaults : ∀ statements, observed.shape.matching.defaultBody = some statements →
        ∃ final facts, StatementsHaveType observed.row.function.typedBody {returnType := .word} context statements final facts := by
      intro statements present; simp [observed.shape.noDefault] at present
    apply GenericImperativeMatch.Syntax.matchWith observed.shape.matchFound observed.shape.matchForm
      (.inl observed.shape.matchType) scrutineeFound (storedType ▸ scrutineeTyped)
      (by rw [observed.shape.scrutinee]; exact leaf _ (by simp [ObservedFactory.readIds]))
      (storedType ▸ casesTyped) defaults
    · simp [observed.shape.inputs, Ne.symm observed.shape.hiddenSeed]
    · intro arm member binder binderMember
      have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
      subst arm
      have sameBinder : binder = observed.shape.copyBinder.id := by
        simpa [TypedMatchPattern.binderIds, observed.shape.patternResolution] using binderMember
      subst binder
      simp [observed.shape.inputs, Ne.symm observed.shape.localSeed]
    · intro request child selected
      have original := requested_body (storedType ▸ casesTyped) defaults selected
      have statements : request.statements = [observed.shape.assignment.id] := by
        cases selected with
        | @arm arm _ _ _ member sameBody _ _ =>
          have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
          subst arm
          exact sameBody.trans observed.shape.armBody
        | default present => simp [observed.shape.noDefault] at present
      rw [statements]
      obtain ⟨final, bodyFacts, bodyTyped⟩ := original
      rw [statements] at bodyTyped
      obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.localRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
          observed.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [ObservedFactory.readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.previousRead observed.shape.innerReturnFound observed.shape.innerReturnForm
        observed.shape.innerReturnType (leaf _ (by simp [ObservedFactory.readIds])) returningHead

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word} context
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have declaration := observed.previous_declaration
  have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.shape.previous.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.previousDistinct]
  cases first with
  | letInitialized contains form initializer _mono _generalized extended _type =>
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
    cases same
    rw [observed.shape.initializedForm] at form
    obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
    cases sameBinder
    cases Option.some.inj sameInitializer
    apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
      declaration mono extended ordinary observed.shape.initialRead.found
      (by rw [observed.shape.initialRead.type, observed.shape.previousScheme]; rfl)
      (by simpa only [observed.shape.initialRead.type, observed.shape.previousScheme, TypeSystem.Scheme.mono] using initializer)
      (leaves _ (by simp [ObservedFactory.readIds]))
    exact tail_syntax observed unique leaves tail
  | letInitializedGeneralized contains form polymorphic _requirements _generalizes _initializer _extended _type =>
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
    cases same
    rw [observed.shape.initializedForm] at form
    obtain ⟨sameBinder, _⟩ := StatementForm.letDecl.inj form
    cases sameBinder
    exact False.elim (polymorphic mono)
  | _ =>
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.initializedFound)
    cases same
    simp_all [observed.shape.initializedForm, observed.shape.previousScheme, TypeSystem.Scheme.mono]

theorem ObservedFactory.body_reads {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word} context
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody) context
      (.statements true [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
  apply observed.body_syntax unique _ typed
  intro id member
  simp only [readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.localRead.found, observed.shape.localRead.form⟩
  · exact ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchSupports
/-! A complete singleton inventory supplies formation and every authentic
captured-read closure body, including the actual nonempty parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
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
    observed.entryMember
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read
  · rw [actual.source]; exact observed.body_shape
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact observed.body_syntax (actual.source ▸ actual.header.unique) (fun _ _ => True.intro) typed


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token, CallableIndexedOwnedPublicDecodedCallFaults.faults
      completion.result.diagnostics reason token → faults reason token) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression receiver included
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩


theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor


theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  input : Input fixture.recipe.compiled
  packet : Issued input
  actual : ActualHeader fixture observed.row
  headerEq : actual.header = packet.header
  rows : Inventory [input]
  rowsEq : rows = .cons packet .nil
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  terminals : ∀ header, header ∈ headers rows → Terminal header
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
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function (.word) .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

theorem static_supports (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory [input] := .cons packet .nil
  have headerList : CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows = [actual.header] := by
    simp only [rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers, sameHeader]
  let stagePrepared := actualStagePrepared fixture
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.expression.id observed.statement
    observed.roots observed.foundStatement observed.returnStatement
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point receiver (fun _ _ proof => proof) (registry := registry) (faults := faults)
  let terminals : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ terminal
  have supports : ∀ header (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows),
      CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (terminals header member) faults := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, ObservedStages.registry, stagePrepared] using support
  have family : ∀ {mapping world function native bindings parameter result}
      (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
        mapping world function native bindings parameter result),
      CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
    intro mapping world function native bindings parameter result association
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
      apply CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic_packets
      have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
      have found := code.sourceFound
      rw [sameSource] at found
      have ⟨_parameters, resultShape, bodyShape⟩ := observed.lambda_shape found code.sourceForm
      have shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape function.source true function.body := by
        rw [sameSource, bodyShape]
        exact observed.body_shape
      have typedBody := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
        support.body.frame support.body.extended
      obtain ⟨_final, _facts, bodyTyped, _completes⟩ := typedBody
      have syntaxTree : GenericImperativeMatch.Syntax function.source
          (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read function.source)
          support.body.context (.statements true function.body) function.resultType := by
        rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
        exact observed.body_reads (sameSource ▸ support.body.unique) bodyTyped
      obtain ⟨sidecar, _issued, selected⟩ :=
        CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
      exact CallableIndexedOwnedPreparedStagedBranchingLambdaReadRoots.of_reads code support provenance receiver
        fixture.source_wellFormed (by rw [sameSource]; exact observed.metadata support.caller.named)
        shape.forget syntaxTree.prepared (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports, family := family, descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchCommon
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted nonzero-parameter factory; retained states refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
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

theorem ObservedPublicRun.start_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      executed.session.IndexedAt session ∧ executed.checkpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word seed] runOptions.inputValidationFuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩


theorem ObservedPublicRun.metadata_at_start {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (executed : ObservedPublicRun fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [.word seed] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  have same : value = .word seed := List.mem_singleton.mp member
  exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedFactory fixture}
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
  registry : session.RegistryAt fixture.recipe.compiled.compatible.checked.staticRegistry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiver.completion.result.context.registry
    support.actual.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.actual.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem statement_roots_injective {left right : List StatementId}
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

private theorem returned_expression
    {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment
      before (id :: rest) finalContext (.returned value) after) :
    Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before
      expression value after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnUnit contains otherForm =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnValue contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact child.sound.value_plain
  | tail contains otherForm _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | discard contains otherForm _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letUninitialized contains otherForm _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letGeneralized contains otherForm _ _ _ _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | bitNotProjected contains otherForm _ _ _ _ _
  | bitNotBare contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem lambda_shape
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {body : List StatementId} {parameters : List TypedBinder}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ function : Dynamic.Closure,
      value = .closure function ∧ function.parameters = parameters ∧ function.resultType = .word := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw
    exact ⟨_, rfl, rfl, rfl⟩
  | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

/-- The existing public factory meaning fixes the exact returned closure,
including its original captures; no closure-shape observation is assumed. -/
theorem SourceCall.make_closure
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.actual.header invocation before [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [observed.argument] ∧ function.resultType = .word := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  have parameters : support.actual.header.function.parameters = [observed.shape.binder] := by
    rw [support.actual.header.parameters, ← support.actual.header.inputs,
      support.actual.source, observed.shape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, _allocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ support.actual.header.unique
  have bodyEq : support.actual.header.function.body = [observed.shape.statement.id] := by
    apply statement_roots_injective
    rw [← support.actual.header.agreement.roots, support.actual.source, observed.shape.roots]
    rfl
  have statementFound : child.source.lookupStatement? observed.shape.statement.id =
      some observed.shape.statement := by
    rw [sourceEq, support.actual.source]
    exact observed.shape.statementFound
  have expressionFound : child.source.lookupExpression? observed.shape.expression.id =
      some observed.shape.expression := by
    rw [sourceEq, support.actual.source]
    exact observed.shape.expressionFound
  rw [support.actual.result_type] at converted
  cases converted
  rw [bodyEq] at body
  exact lambda_shape unique expressionFound observed.shape.lambda observed.shape.coercions
    (returned_expression unique statementFound observed.shape.returnStatement body)

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchInvocation
/-! Actual one-Word public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (argument : Core.Word) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [.word argument] outcome after

/-- Both the packed argument and callee meaning come from the original encoder
and current History. The returned state uses this call's exact public completion. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .word .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    (parameters : function.parameters = [observed.argument])
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .word .word)
    {argument : Core.Word} (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source argument (.value (.word word)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .word (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
      after, finalMap, finalWorld, reached, started, _parameterView, _resultView, succeeded,
      actualAt, packing, arity, trace, result, _related, retained, _encodedRegistry, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectPackedPublicHistory.public_invoke_succeeded_function_tree
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple (.word argument))
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function .word .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [.word argument] :=
    packing.injective_of_length_eq (.singleton (.word argument)) (by simpa [parameters] using arity)
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, sourcesEq, outcomeValue] using trace

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedFactory fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .word .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .word .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.actual.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.actual.header := by
    have member := (congrArg (fun items => request.header ∈ items) support.header_list).mp request.selected.member
    exact List.mem_singleton.mp member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.actual.input_types]
    exact .cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil
  have registryAt : request.encodedValues.registry =
      fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word word := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word word
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.descriptor
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact receiver.completion.result.extension)
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
  rw [resultType, selected, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function .word .word
    rw [selected]
    exact support.actual.result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed)
    (first : ObservedPublicRun fixture observed) :
    ∃ entry : Entry,
      entry.sourceType = .function .word .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .word .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.actual.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    first.start_receipt
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry :=
    first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.started first.executed first.returned support.descriptor
  let entry : Entry := ⟨support.actual.header.function.resultType, source, first.handle,
    payload, support.actual.header.output, runOptions.outputValidationFuel⟩
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
    registry := returnedRegistry
    history := retained }
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.actual.result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.input.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩


end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchPublicExecution
/-! The first closure is called again after a separate closure and a fresh
factory allocation, and its second call starts again from its captured seed:
the write of its first call does not carry over. Every transition uses the
actual returned public session and the same Source heap retained by the
previous call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function .word .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function .word .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function .word .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.argument] ∧ secondClosure.parameters = [observed.argument] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source (Core.Word.ofNatModulo 11)
          (.value (.word (Core.Word.ofNatModulo 10))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source (Core.Word.ofNatModulo 21)
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source (Core.Word.ofNatModulo 12)
          (.value (.word (Core.Word.ofNatModulo 10))) final.heap

/-- Accepted checker/compiler observations construct all static support. After
independent activity the first closure reads its captured seed again: the
match's write in its first call does not carry over. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := receiver.completion) fixture observed stages receiver.completion.result.context.registry
    (receiver.issued)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨firstEntry, firstType, firstHandle, firstHandleType, first, firstTrace⟩ :=
    first_meaning support stages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨secondEntry, secondType, secondHandle, secondHandleType, second, secondTrace⟩ :=
    first.make_typed_handle sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨written, writtenTrace⟩ := invoke second firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstCall sequence.firstValue scope
  obtain ⟨thirdEntry, thirdType, thirdHandle, _thirdHandleType, third, thirdTrace⟩ :=
    written.make_typed_handle sequence.third scope
  obtain ⟨other, otherTrace⟩ := invoke third secondEntry (by simp) secondType secondSource
    secondParameters secondHandle secondHandleType sequence.secondCall sequence.secondValue scope
  obtain ⟨final, finalTrace⟩ := invoke other firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstAgain sequence.finalValue scope
  have distinct : firstEntry.handle ≠ secondEntry.handle := by
    rw [firstHandle, secondHandle]
    exact sequence.distinct
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩

/-- All static and receiving evidence comes from the actual accepted compiler
and authentic registry. No external receiver or body meaning is required. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ receiver, SequenceMeaning stages sequence receiver := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed stages sequence receiver⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual captured match: make10/make20, first11 returns10, make30, second21 returns20, first12 returns10; six Source calls and returned histories proved"

end Tests.SourceCoreCapturedMatch
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMatchForward
/-! The actual match calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMatch
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument : Core.Word) (word : Core.Word)
    (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (.word argument) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ required, ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      required ≤ executionFuel → 1 ≤ outputFuel →
      checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .word .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument word : Core.Word} (call : ObservedInvocation publicSession handle argument)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceInvocation support invocation state.heap entry.source argument (.value (.word word)) after) :
    ForwardWordAt support publicSession entries handle argument word after := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled receiver.issued)
  obtain ⟨publicCheckpoint, accepted, _resumed⟩ := call.executed
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType, entryHandle] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.current.1 imported original
  have registryEq := started.function_tree_registry (.simple (.word argument)) state.registry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [registryEq]
    exact receiver.completion.result.extension
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .word
      (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
  obtain ⟨size, trace⟩ := trace
  rw [entrySource] at trace
  rw [← entryHandle] at started
  obtain ⟨required, finalStore, finalMap, finalWorld, _nativeEnough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicDirectWordPreservation.public_resume_has_sufficient_fuel
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) started metadata (.singleton (.word argument)) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function .word .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function .word .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function .word .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.argument] ∧ secondClosure.parameters = [observed.argument] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source (Core.Word.ofNatModulo 11)
          (.value (.word (Core.Word.ofNatModulo 10))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source (Core.Word.ofNatModulo 21)
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source (Core.Word.ofNatModulo 12)
          (.value (.word (Core.Word.ofNatModulo 10))) final.heap ∧
        ForwardWordAt support sequence.second.completion.session [firstEntry, secondEntry] sequence.first.handle
          (Core.Word.ofNatModulo 11) (Core.Word.ofNatModulo 10) written.heap ∧
        ForwardWordAt support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry] sequence.second.handle
          (Core.Word.ofNatModulo 21) (Core.Word.ofNatModulo 20) other.heap ∧
        ForwardWordAt support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry] sequence.first.handle
          (Core.Word.ofNatModulo 12) (Core.Word.ofNatModulo 10) final.heap

/-- All three calls have a forward public
fuel guarantee on their original checkpoints, with exact Source post-heaps. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed)
    (receiver : ObservedReceiver fixture observed) : ForwardMeaning stages sequence receiver := by
  obtain ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
      firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
      firstSource, secondSource, firstParameters, secondParameters,
      first, second, written, third, other, final,
      firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩ :=
    sequence_meaning fixture observed stages sequence receiver
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace,
    forward_word second firstEntry (by simp) firstType firstSource firstHandle sequence.firstCall writtenTrace,
    forward_word third secondEntry (by simp) secondType secondSource secondHandle sequence.secondCall otherTrace,
    forward_word other firstEntry (by simp) firstType firstSource firstHandle sequence.firstAgain finalTrace⟩

/-- All static and receiving evidence comes from the actual accepted compiler
and authentic registry. No external receiver or body meaning is required. -/
theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ receiver, ForwardMeaning stages sequence receiver := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_forward_meaning fixture observed stages sequence receiver⟩

/-- The observed scenario is shared by reflection and forward preservation. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed stages sequence
  IO.println "Actual captured match: independent Source traces, returned histories and sufficient public Word export fuel proved for all three direct calls"

end Tests.SourceCoreCapturedMatch
end
