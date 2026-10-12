import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Independent Source typing for a closure with a finite loop updating its capture and condition cell. -/
namespace Tests.SourceCoreCapturedWhile
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
  stop : TypedBinder
  conditionRead : BoolRead function.typedBody flag
  argumentRead : WordRead function.typedBody argument
  stopRead : BoolRead function.typedBody stop
  finalRead : WordRead function.typedBody binder
  assignment : StatementNode
  resolution : AssignmentResolution
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
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
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOwner : stop.id.owner = function.typedBody.owner
  stopDistinct : stop.id ≠ binder.id
  stopFlag : stop.id ≠ flag.id
  stopArgument : stop.id ≠ argument.id
  parameterNames : [flag.name, argument.name, stop.name].Nodup
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function (.product .bool (.product .word .bool)) .word]
  inputs : function.typedBody.inputs = [binder]
  binderOwner : binder.id.owner = function.typedBody.owner
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal argumentRead.node.id
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
  innerReturnForm : innerReturn.form = .returnStmt (some finalRead.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [flag, argument, stop] .word [loop.id, innerReturn.id]
  expressionRaw : expression.rawType = .function (.product .bool (.product .word .bool)) .word
  expressionType : expression.type = .function (.product .bool (.product .word .bool)) .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function (.product .bool (.product .word .bool)) .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.innerReturn.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.argumentRead.node,
    .statement shape.assignment, .expression shape.stopRead.node, .statement shape.flagAssignment,
    .statement shape.loop, .expression shape.finalRead.node, .statement shape.innerReturn,
    .expression shape.expression, .statement shape.statement]

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
  let facts : StatementFacts := {type := .function (.product .bool (.product .word .bool)) .word, hasValue := true, sawReturn := true, control := .returned}
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
    have callable : TypeAdmissible lexical (.function (.product .bool (.product .word .bool)) .word) :=
      ⟨binders, .function (.product (.builtin .bool) (.product (.builtin .word) (.builtin .bool))) (.builtin .word)⟩
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
    let locals := arguments.withLocal shape.stop.id shape.stop.scheme shape.stop.schemeRequirements
    have stopExtended : BinderExtends function.typedBody.owner arguments shape.stop locals := by
      apply BinderExtends.intro
      · exact {
          owned := shape.stopOwner
          scheme := shape.stopScheme.symm ▸ SchemeWellFormed.monoAdmissible argumentBool
          quantified_fresh := by rw [shape.stopScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.stopRequirements }
      · cases head
        simp [arguments, flags, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.stopDistinct, shape.stopArgument, shape.stopFlag]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localBool : TypeAdmissible locals .bool := ⟨binders, .builtin .bool⟩
    have seedLookup : locals.LocalLookup shape.binder.id shape.binder.scheme :=
      .tail shape.stopDistinct (.tail shape.argumentDistinct (.tail shape.flagDistinct head.local_self))
    have seedRequirements : locals.LocalSchemeRequirementsLookup shape.binder.id shape.binder.schemeRequirements :=
      .tail shape.stopDistinct (.tail shape.argumentDistinct (.tail shape.flagDistinct head.local_scheme_requirements_self))
    have flagLookup : locals.LocalLookup shape.flag.id shape.flag.scheme :=
      .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_self)
    have flagRequirements : locals.LocalSchemeRequirementsLookup shape.flag.id shape.flag.schemeRequirements :=
      .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements localBool flagLookup flagRequirements
    have rhsTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements localWord
      (.tail shape.stopArgument argumentExtended.local_self) (.tail shape.stopArgument argumentExtended.local_scheme_requirements_self)
    have stopTyped := shape.stopRead.typed shape.stopScheme shape.stopRequirements localBool
      stopExtended.local_self stopExtended.local_scheme_requirements_self
    have finalTyped := shape.finalRead.typed scheme shape.binderRequirements localWord seedLookup seedRequirements
    have writable : WritableLocal locals shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro seedLookup (scheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.argumentRead.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word, 1⟩ locals shape.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have flagWritable : WritableLocal locals shape.flagResolution.target.root .bool := by
      rw [shape.flagTargetRoot]
      exact .intro flagLookup (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible localBool)
        (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
    have flagAssignmentTyped : SourceAssignmentHasType function.typedBody locals shape.flagResolution .equal shape.stopRead.node.id :=
      .equal (.intro flagWritable (by rw [shape.flagTargetBare]; exact .nil _) shape.flagTargetType) stopTyped shape.flagAssignmentRequirements
    have flagTyped : StatementHasType function.typedBody ⟨.word, 1⟩ locals shape.flagAssignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.flagAssignmentFound) shape.flagAssignmentForm flagAssignmentTyped shape.flagAssignmentType
    have loopTyped := StatementHasType.whileLoop (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped
      (.cons statementTyped (.singleton flagTyped)) shape.loopType
    have innerReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm finalTyped shape.innerReturnType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id (.function (.product .bool (.product .word .bool)) .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simpa only [List.map_cons, List.map_nil] using shape.parameterNames)
          (.cons shape.flagScheme flagExtended (.cons shape.argumentScheme argumentExtended (.cons shape.stopScheme stopExtended (.nil _))))
          (.cons loopTyped (.singleton innerReturnTyped))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Bool, Word, Bool) returns (Word)) { return lam(flag: Bool, next: Word, stop: Bool) { while (flag) { seed = next; flag = stop; } return seed; }; }"}] }

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
  let [.expression condition, .expression rhs, .statement assignment, .expression stopValue,
      .statement flagAssignment, .statement loop, .expression final, .statement innerReturn,
      .expression expression, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "while factory graph")
  let .lambda [flag, argument, stop] _ _ := expression.form | throw (IO.userError "while parameters")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "capture assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "condition assignment")
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let argumentRead ← observeRead function.typedBody argument rhs .word
  let stopRead ← observeRead function.typedBody stop stopValue .bool
  let finalRead ← observeRead function.typedBody binder final .word
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "while factory flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "while factory flagRequirements"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "while factory flagOwner"
  let ⟨flagDistinct⟩ ← observed (flag.id ≠ binder.id) "while factory flagDistinct"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "while factory argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "while factory argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "while factory argumentOwner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "while factory argumentDistinct"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "while factory argumentFlag"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "while factory stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "while factory stopRequirements"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "while factory stopOwner"
  let ⟨stopDistinct⟩ ← observed (stop.id ≠ binder.id) "while factory stopDistinct"
  let ⟨stopFlag⟩ ← observed (stop.id ≠ flag.id) "while factory stopFlag"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "while factory stopArgument"
  let ⟨parameterNames⟩ ← observed ([flag.name, argument.name, stop.name].Nodup) "while factory parameterNames"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "while factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "while factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function (.product .bool (.product .word .bool)) .word]) "while factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "while factory inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "while factory binderOwner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "while factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "while factory roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "while factory assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "while factory assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "while factory assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "while factory targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "while factory targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "while factory targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "while factory assignmentRequirements"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "while factory flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stopRead.node.id) "while factory flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "while factory flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "while factory flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "while factory flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "while factory flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "while factory flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "while factory loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "while factory loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "while factory loopType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "while factory innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some finalRead.node.id)) "while factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "while factory innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "while factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "while factory statementFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [flag, argument, stop] .word [loop.id, innerReturn.id]) "while factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function (.product .bool (.product .word .bool)) .word) "while factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function (.product .bool (.product .word .bool)) .word) "while factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "while factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "while factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "while factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function (.product .bool (.product .word .bool)) .word) "while factory statementType"
  return {binder, flag, argument, stop, conditionRead, argumentRead, stopRead, finalRead, assignment, resolution, flagAssignment, flagResolution, loop, innerReturn, expression, statement, flagScheme, flagRequirements, flagOwner, flagDistinct, argumentScheme, argumentRequirements, argumentOwner, argumentDistinct, argumentFlag, stopScheme, stopRequirements, stopOwner, stopDistinct, stopFlag, stopArgument, parameterNames, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, statementFound, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType}

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete while factory graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected while factory methods")
    | _, _ => throw (IO.userError "while factory declaration count")

end Tests.SourceCoreCapturedWhile
