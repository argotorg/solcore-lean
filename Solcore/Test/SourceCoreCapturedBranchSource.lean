import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Independent Source typing for a closure with scoped conditional writes and early return. -/
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
