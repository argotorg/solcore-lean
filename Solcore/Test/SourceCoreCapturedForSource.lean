import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Independent Source typing for a captured update with scoped for initialization and post, returning the previous captured Word. -/
namespace Tests.SourceCoreCapturedFor
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
  running : TypedBinder
  argument : TypedBinder
  stop : TypedBinder
  previous : TypedBinder
  flag : TypedBinder
  initialRead : WordRead function.typedBody binder
  headerRead : BoolRead function.typedBody running
  conditionRead : BoolRead function.typedBody flag
  argumentRead : WordRead function.typedBody argument
  stopRead : BoolRead function.typedBody stop
  finalRead : WordRead function.typedBody previous
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
  postResolution : AssignmentResolution
  loop : StatementNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  runningScheme : running.scheme = .mono .bool
  runningRequirements : running.schemeRequirements = []
  runningOwner : running.id.owner = function.typedBody.owner
  runningOrdinary : running.comptime = false
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentOrdinary : argument.comptime = false
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOwner : stop.id.owner = function.typedBody.owner
  stopOrdinary : stop.comptime = false
  previousScheme : previous.scheme = .mono .word
  previousRequirements : previous.schemeRequirements = []
  previousOwner : previous.id.owner = function.typedBody.owner
  previousOrdinary : previous.comptime = false
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOwner : flag.id.owner = function.typedBody.owner
  flagOrdinary : flag.comptime = false
  runningDistinct : running.id ≠ binder.id
  argumentDistinct : argument.id ≠ binder.id
  argumentRunning : argument.id ≠ running.id
  stopDistinct : stop.id ≠ binder.id
  stopRunning : stop.id ≠ running.id
  stopArgument : stop.id ≠ argument.id
  previousDistinct : previous.id ≠ binder.id
  previousRunning : previous.id ≠ running.id
  previousArgument : previous.id ≠ argument.id
  previousStop : previous.id ≠ stop.id
  flagDistinct : flag.id ≠ binder.id
  flagRunning : flag.id ≠ running.id
  flagArgument : flag.id ≠ argument.id
  flagStop : flag.id ≠ stop.id
  flagPrevious : flag.id ≠ previous.id
  parameterNames : [running.name, argument.name, stop.name].Nodup
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function (.product .bool (.product .word .bool)) .word]
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
  postRoot : postResolution.target.root = flag.id
  postType : postResolution.target.type = .bool
  postBare : postResolution.target.projections = []
  postRequirements : postResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl flag (some headerRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]
  loopType : loop.type = .unit
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  innerReturnForm : innerReturn.form = .returnStmt (some finalRead.node.id)
  innerReturnType : innerReturn.type = .word
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [running, argument, stop] .word [initialized.id, loop.id, innerReturn.id]
  expressionRaw : expression.rawType = .function (.product .bool (.product .word .bool)) .word
  expressionType : expression.type = .function (.product .bool (.product .word .bool)) .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function (.product .bool (.product .word .bool)) .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.initialized.id, shape.loop.id, shape.innerReturn.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .statement shape.initialized, .expression shape.headerRead.node,
    .expression shape.conditionRead.node, .expression shape.argumentRead.node, .statement shape.assignment,
    .expression shape.stopRead.node, .statement shape.loop, .expression shape.finalRead.node,
    .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]

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
    let runnings := lexical.withLocal shape.running.id shape.running.scheme shape.running.schemeRequirements
    have runningExtended : BinderExtends function.typedBody.owner lexical shape.running runnings := by
      apply BinderExtends.intro
      · exact {
          owned := shape.runningOwner
          scheme := shape.runningScheme.symm ▸ SchemeWellFormed.monoAdmissible bool
          quantified_fresh := by rw [shape.runningScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.runningRequirements }
      · cases head
        simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.runningDistinct]
    have runningWord : TypeAdmissible runnings .word := ⟨binders, .builtin .word⟩
    let arguments := runnings.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner runnings shape.argument arguments := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible runningWord
          quantified_fresh := by rw [shape.argumentScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
          monomorphic_requirements_empty := fun _ => shape.argumentRequirements }
      · cases head
        simp [runnings, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.argumentDistinct, shape.argumentRunning]
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
        simp [arguments, runnings, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.stopDistinct, shape.stopArgument, shape.stopRunning]
    have localWord : TypeAdmissible locals .word := ⟨binders, .builtin .word⟩
    have localBool : TypeAdmissible locals .bool := ⟨binders, .builtin .bool⟩
    let saved := locals.withLocal shape.previous.id shape.previous.scheme shape.previous.schemeRequirements
    have previousExtended : BinderExtends function.typedBody.owner locals shape.previous saved := by
      apply BinderExtends.intro
      · exact { owned := shape.previousOwner
                scheme := shape.previousScheme.symm ▸ SchemeWellFormed.monoAdmissible localWord
                quantified_fresh := by rw [shape.previousScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                monomorphic_requirements_empty := fun _ => shape.previousRequirements }
      · cases head
        simp [locals, arguments, runnings, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.previousDistinct, shape.previousRunning, shape.previousArgument, shape.previousStop]
    have savedWord : TypeAdmissible saved .word := ⟨binders, .builtin .word⟩
    have savedBool : TypeAdmissible saved .bool := ⟨binders, .builtin .bool⟩
    let loopContext := saved.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
    have flagExtended : BinderExtends function.typedBody.owner saved shape.flag loopContext := by
      apply BinderExtends.intro
      · exact { owned := shape.flagOwner
                scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible savedBool
                quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                monomorphic_requirements_empty := fun _ => shape.flagRequirements }
      · cases head
        simp [saved, locals, arguments, runnings, LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
          Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withResidualTypeVariables,
          shape.flagDistinct, shape.flagRunning, shape.flagArgument, shape.flagStop, shape.flagPrevious]
    have loopWord : TypeAdmissible loopContext .word := ⟨binders, .builtin .word⟩
    have loopBool : TypeAdmissible loopContext .bool := ⟨binders, .builtin .bool⟩
    have seedLookup : locals.LocalLookup shape.binder.id shape.binder.scheme :=
      .tail shape.stopDistinct (.tail shape.argumentDistinct (.tail shape.runningDistinct head.local_self))
    have seedRequirements : locals.LocalSchemeRequirementsLookup shape.binder.id shape.binder.schemeRequirements :=
      .tail shape.stopDistinct (.tail shape.argumentDistinct (.tail shape.runningDistinct head.local_scheme_requirements_self))
    have initialTyped := shape.initialRead.typed scheme shape.binderRequirements localWord seedLookup seedRequirements
    have initializedTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.initialized.id saved ordinary := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.previousScheme, TypeSystem.Scheme.mono] using initialTyped
      · rw [shape.previousScheme]; rfl
      · rw [shape.previousScheme]; rfl
      · exact previousExtended
      · exact shape.initializedType
    have headerTyped := shape.headerRead.typed shape.runningScheme shape.runningRequirements savedBool
      (.tail shape.previousRunning (.tail shape.stopRunning (.tail shape.argumentRunning runningExtended.local_self)))
      (.tail shape.previousRunning (.tail shape.stopRunning (.tail shape.argumentRunning runningExtended.local_scheme_requirements_self)))
    have initialized : ForItemsHaveType function.typedBody ⟨.word, 0⟩ saved
        [.letDecl shape.flag (some shape.headerRead.node.id)] loopContext := by
      refine .cons (.letInitialized ?_ ?_ ?_ flagExtended) (.nil _ _)
      · simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using headerTyped
      · rw [shape.flagScheme]; rfl
      · rw [shape.flagScheme]; rfl
    have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements loopBool
      flagExtended.local_self flagExtended.local_scheme_requirements_self
    have rhsTyped := shape.argumentRead.typed shape.argumentScheme shape.argumentRequirements loopWord
      (.tail shape.flagArgument (.tail shape.previousArgument (.tail shape.stopArgument argumentExtended.local_self)))
      (.tail shape.flagArgument (.tail shape.previousArgument (.tail shape.stopArgument argumentExtended.local_scheme_requirements_self)))
    have stopTyped := shape.stopRead.typed shape.stopScheme shape.stopRequirements loopBool
      (.tail shape.flagStop (.tail shape.previousStop stopExtended.local_self))
      (.tail shape.flagStop (.tail shape.previousStop stopExtended.local_scheme_requirements_self))
    have finalTyped := shape.finalRead.typed shape.previousScheme shape.previousRequirements savedWord
      previousExtended.local_self previousExtended.local_scheme_requirements_self
    have writable : WritableLocal loopContext shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro (.tail shape.flagDistinct (.tail shape.previousDistinct seedLookup))
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible loopWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody loopContext shape.resolution .equal shape.argumentRead.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word, 1⟩ loopContext shape.assignment.id loopContext ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have flagWritable : WritableLocal loopContext shape.postResolution.target.root .bool := by
      rw [shape.postRoot]
      exact .intro flagExtended.local_self (shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible loopBool)
        (by rw [shape.flagScheme]; rfl) (by rw [shape.flagScheme]; rfl)
    have postTyped : ForItemsHaveType function.typedBody ⟨.word, 1⟩ loopContext
        [.assignValue shape.postResolution .equal shape.stopRead.node.id] loopContext :=
      .cons (.assignValue (.equal (.intro flagWritable (by rw [shape.postBare]; exact .nil _) shape.postType)
        stopTyped shape.postRequirements)) (.nil _ _)
    have loopTyped := StatementHasType.forLoop (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm initialized conditionTyped (.singleton statementTyped) postTyped shape.loopType
    have innerReturnTyped := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.innerReturnFound) shape.innerReturnForm finalTyped shape.innerReturnType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id (.function (.product .bool (.product .word .bool)) .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simpa only [List.map_cons, List.map_nil] using shape.parameterNames)
          (.cons shape.runningScheme runningExtended (.cons shape.argumentScheme argumentExtended (.cons shape.stopScheme stopExtended (.nil _))))
          (.cons initializedTyped (.cons loopTyped (.singleton innerReturnTyped)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound) shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Bool, Word, Bool) returns (Word)) { return lam(running: Bool, next: Word, done: Bool) { let previous: Word = seed; for (let flag: Bool = running; flag; flag = done) { seed = next; } return previous; }; }"}] }
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
  let [.expression initial, .statement initialized, .expression header,
      .expression condition, .expression rhs, .statement assignment, .expression post,
      .statement loop, .expression old, .statement innerReturn, .expression expression,
      .statement statement] := function.typedBody.nodes | throw (IO.userError "captured for nodes")
  let .lambda [running, argument, stop] _ _ := expression.form | throw (IO.userError "lambda parameters")
  let .letDecl previous _ := initialized.form | throw (IO.userError "previous local")
  let .forLoop [.letDecl flag _] _ [.assignValue postResolution .equal _] _ := loop.form | throw (IO.userError "for header")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "body assignment")
  let initialRead ← observeRead function.typedBody binder initial .word
  let headerRead ← observeRead function.typedBody running header .bool
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let argumentRead ← observeRead function.typedBody argument rhs .word
  let stopRead ← observeRead function.typedBody stop post .bool
  let finalRead ← observeRead function.typedBody previous old .word
  let ⟨runningScheme⟩ ← observed (running.scheme = .mono .bool) "captured for runningScheme"
  let ⟨runningRequirements⟩ ← observed (running.schemeRequirements = []) "captured for runningRequirements"
  let ⟨runningOwner⟩ ← observed (running.id.owner = function.typedBody.owner) "captured for runningOwner"
  let ⟨runningOrdinary⟩ ← observed (running.comptime = false) "captured for runningOrdinary"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "captured for argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "captured for argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "captured for argumentOwner"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "captured for argumentOrdinary"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "captured for stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "captured for stopRequirements"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "captured for stopOwner"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "captured for stopOrdinary"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "captured for previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "captured for previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "captured for previousOwner"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "captured for previousOrdinary"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "captured for flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "captured for flagRequirements"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "captured for flagOwner"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "captured for flagOrdinary"
  let ⟨runningDistinct⟩ ← observed (running.id ≠ binder.id) "captured for runningDistinct"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "captured for argumentDistinct"
  let ⟨argumentRunning⟩ ← observed (argument.id ≠ running.id) "captured for argumentRunning"
  let ⟨stopDistinct⟩ ← observed (stop.id ≠ binder.id) "captured for stopDistinct"
  let ⟨stopRunning⟩ ← observed (stop.id ≠ running.id) "captured for stopRunning"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "captured for stopArgument"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "captured for previousDistinct"
  let ⟨previousRunning⟩ ← observed (previous.id ≠ running.id) "captured for previousRunning"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "captured for previousArgument"
  let ⟨previousStop⟩ ← observed (previous.id ≠ stop.id) "captured for previousStop"
  let ⟨flagDistinct⟩ ← observed (flag.id ≠ binder.id) "captured for flagDistinct"
  let ⟨flagRunning⟩ ← observed (flag.id ≠ running.id) "captured for flagRunning"
  let ⟨flagArgument⟩ ← observed (flag.id ≠ argument.id) "captured for flagArgument"
  let ⟨flagStop⟩ ← observed (flag.id ≠ stop.id) "captured for flagStop"
  let ⟨flagPrevious⟩ ← observed (flag.id ≠ previous.id) "captured for flagPrevious"
  let ⟨parameterNames⟩ ← observed ([running.name, argument.name, stop.name].Nodup) "captured for parameterNames"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured for parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured for inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function (.product .bool (.product .word .bool)) .word]) "captured for returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured for inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "captured for binderOwner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured for binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured for roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "captured for initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initialRead.node.id)) "captured for initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "captured for initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "captured for assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "captured for assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "captured for assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "captured for targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "captured for targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "captured for targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "captured for assignmentRequirements"
  let ⟨postRoot⟩ ← observed (postResolution.target.root = flag.id) "captured for postRoot"
  let ⟨postType⟩ ← observed (postResolution.target.type = .bool) "captured for postType"
  let ⟨postBare⟩ ← observed (postResolution.target.projections = []) "captured for postBare"
  let ⟨postRequirements⟩ ← observed (postResolution.requirements = []) "captured for postRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "captured for loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl flag (some headerRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]) "captured for loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "captured for loopType"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured for innerReturnFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some finalRead.node.id)) "captured for innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured for innerReturnType"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured for expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured for statementFound"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [running, argument, stop] .word [initialized.id, loop.id, innerReturn.id]) "captured for lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function (.product .bool (.product .word .bool)) .word) "captured for expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function (.product .bool (.product .word .bool)) .word) "captured for expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured for requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured for coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured for returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function (.product .bool (.product .word .bool)) .word) "captured for statementType"
  return { binder, running, argument, stop, previous, flag, initialRead, headerRead, conditionRead, argumentRead, stopRead, finalRead, initialized, assignment, resolution, postResolution, loop, innerReturn, expression, statement, runningScheme, runningRequirements, runningOwner, runningOrdinary, argumentScheme, argumentRequirements, argumentOwner, argumentOrdinary, stopScheme, stopRequirements, stopOwner, stopOrdinary, previousScheme, previousRequirements, previousOwner, previousOrdinary, flagScheme, flagRequirements, flagOwner, flagOrdinary, runningDistinct, argumentDistinct, argumentRunning, stopDistinct, stopRunning, stopArgument, previousDistinct, previousRunning, previousArgument, previousStop, flagDistinct, flagRunning, flagArgument, flagStop, flagPrevious, parameterNames, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, postRoot, postType, postBare, postRequirements, loopFound, loopForm, loopType, innerReturnFound, innerReturnForm, innerReturnType, expressionFound, statementFound, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

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

end Tests.SourceCoreCapturedFor
