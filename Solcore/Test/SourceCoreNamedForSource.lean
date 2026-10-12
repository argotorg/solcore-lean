import Solcore.Test.SourceCoreNamedWhileSource
/-! Independent Source typing for a scoped for-header local, body mutation,
post update and restored outer return. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedWhile.Read

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  value : TypedBinder
  argument : TypedBinder
  running : TypedBinder
  stop : TypedBinder
  flag : TypedBinder
  initialRead : Read function.typedBody running .bool
  conditionRead : Read function.typedBody flag .bool
  argumentRead : Read function.typedBody argument .word
  stopRead : Read function.typedBody stop .bool
  finalRead : Read function.typedBody value .word
  assignment : StatementNode
  resolution : AssignmentResolution
  postResolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  valueScheme : value.scheme = .mono .word
  valueRequirements : value.schemeRequirements = []
  valueOrdinary : value.comptime = false
  valueOwner : value.id.owner = function.typedBody.owner
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentOwner : argument.id.owner = function.typedBody.owner
  runningScheme : running.scheme = .mono .bool
  runningRequirements : running.schemeRequirements = []
  runningOrdinary : running.comptime = false
  runningOwner : running.id.owner = function.typedBody.owner
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOrdinary : stop.comptime = false
  stopOwner : stop.id.owner = function.typedBody.owner
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  flagOwner : flag.id.owner = function.typedBody.owner
  argumentValue : argument.id ≠ value.id
  runningValue : running.id ≠ value.id
  runningArgument : running.id ≠ argument.id
  stopValue : stop.id ≠ value.id
  stopArgument : stop.id ≠ argument.id
  stopRunning : stop.id ≠ running.id
  flagValue : flag.id ≠ value.id
  flagArgument : flag.id ≠ argument.id
  flagRunning : flag.id ≠ running.id
  flagStop : flag.id ≠ stop.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word, .word, .bool, .bool]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [value, argument, running, stop]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal argumentRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = value.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  postRoot : postResolution.target.root = flag.id
  postType : postResolution.target.type = .bool
  postBare : postResolution.target.projections = []
  postRequirements : postResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .forLoop [.letDecl flag (some initialRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]
def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.initialRead.node, .expression shape.conditionRead.node, .expression shape.argumentRead.node,
    .statement shape.assignment, .expression shape.stopRead.node, .statement shape.loop,
    .expression shape.finalRead.node, .statement shape.statement]

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
  have same : statements = [shape.loop.id, shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let ordinary : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons ordinary (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons valueScheme valueExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail with
      | cons runningScheme runningExtended tail =>
        cases tail with
        | cons stopScheme stopExtended tail =>
          cases tail
          have binders : TypeParameterBindersWellFormed lexical := by
            rw [TypeParameterBindersWellFormed, stopExtended.context_fields.2.2.1,
              runningExtended.context_fields.2.2.1, argumentExtended.context_fields.2.2.1,
              valueExtended.context_fields.2.2.1]
            simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
              Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
          have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
          have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
          let loopContext := lexical.withLocal shape.flag.id shape.flag.scheme shape.flag.schemeRequirements
          have flagExtended : BinderExtends function.typedBody.owner lexical shape.flag loopContext := by
            apply BinderExtends.intro
            · exact {owned := shape.flagOwner
                     scheme := shape.flagScheme.symm ▸ SchemeWellFormed.monoAdmissible bool
                     quantified_fresh := by rw [shape.flagScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
                     monomorphic_requirements_empty := fun _ => shape.flagRequirements}
            · cases stopExtended; cases runningExtended; cases argumentExtended; cases valueExtended
              simp [LocalFresh, Context.withLocal, checkedBodyContext, declarationContext,
                Context.ofSignatures, Context.forDeclaration, Context.withAssumptions,
                Context.withSolvedRequirements, Context.withResidualTypeVariables,
                shape.flagValue, shape.flagArgument, shape.flagRunning, shape.flagStop]
          have loopWord : TypeAdmissible loopContext .word := ⟨binders, .builtin .word⟩
          have loopBool : TypeAdmissible loopContext .bool := ⟨binders, .builtin .bool⟩
          have initialTyped := shape.initialRead.typed runningScheme shape.runningRequirements bool
            (by cases stopExtended; exact .tail shape.stopRunning runningExtended.local_self)
            (by cases stopExtended; exact .tail shape.stopRunning runningExtended.local_scheme_requirements_self)
          have initialized : ForItemsHaveType function.typedBody ⟨.word, 0⟩ lexical
              [.letDecl shape.flag (some shape.initialRead.node.id)] loopContext := by
            refine .cons (.letInitialized ?_ ?_ ?_ flagExtended) (.nil _ _)
            · simpa only [shape.flagScheme, TypeSystem.Scheme.mono] using initialTyped
            · rw [shape.flagScheme]; rfl
            · rw [shape.flagScheme]; rfl
          have conditionTyped := shape.conditionRead.typed shape.flagScheme shape.flagRequirements loopBool
            flagExtended.local_self flagExtended.local_scheme_requirements_self
          have argumentTyped := shape.argumentRead.typed argumentScheme shape.argumentRequirements loopWord
            (by cases stopExtended; cases runningExtended
                exact .tail shape.flagArgument (.tail shape.stopArgument (.tail shape.runningArgument argumentExtended.local_self)))
            (by cases stopExtended; cases runningExtended
                exact .tail shape.flagArgument (.tail shape.stopArgument (.tail shape.runningArgument argumentExtended.local_scheme_requirements_self)))
          have stopTyped := shape.stopRead.typed stopScheme shape.stopRequirements loopBool
            (.tail shape.flagStop stopExtended.local_self) (.tail shape.flagStop stopExtended.local_scheme_requirements_self)
          have valueLookup : lexical.LocalLookup shape.value.id shape.value.scheme := by
            cases stopExtended; cases runningExtended; cases argumentExtended
            exact .tail shape.stopValue (.tail shape.runningValue (.tail shape.argumentValue valueExtended.local_self))
          have valueRequirements : lexical.LocalSchemeRequirementsLookup shape.value.id shape.value.schemeRequirements := by
            cases stopExtended; cases runningExtended; cases argumentExtended
            exact .tail shape.stopValue (.tail shape.runningValue (.tail shape.argumentValue valueExtended.local_scheme_requirements_self))
          have finalTyped := shape.finalRead.typed valueScheme shape.valueRequirements word valueLookup valueRequirements
          have valueWritable : WritableLocal loopContext shape.resolution.target.root .word := by
            rw [shape.targetRoot]
            exact .intro (.tail shape.flagValue valueLookup)
              (valueScheme.symm ▸ SchemeWellFormed.monoAdmissible loopWord)
              (by rw [valueScheme]; rfl) (by rw [valueScheme]; rfl)
          have assignmentTyped : SourceAssignmentHasType function.typedBody loopContext shape.resolution .equal shape.argumentRead.node.id :=
            .equal (.intro valueWritable (by rw [shape.targetBare]; exact .nil _) shape.targetType)
              argumentTyped shape.assignmentRequirements
          have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ loopContext shape.assignment.id loopContext ordinary :=
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
            (lookupStatement?_sound shape.loopFound) shape.loopForm initialized conditionTyped (.singleton assigned) postTyped shape.loopType
          have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
            (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
          exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function update(value: Word, next: Word, running: Bool, done: Bool) returns (Word) { for (let flag: Bool = running; flag; flag = done) { value = next; } return value; }"}] }
private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)
abbrev observeRead := Tests.SourceCoreNamedWhile.observeRead

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [value, argument, running, stop] := function.typedBody.inputs | throw (IO.userError "named for inputs")
  let [.expression initial, .expression condition, .expression rhs, .statement assignment,
       .expression post, .statement loop, .expression finalNode, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named for nodes")
  let .forLoop [.letDecl flag _] _ [.assignValue postResolution .equal _] _ := loop.form
    | throw (IO.userError "named for header")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "named for assignment")
  let initialRead ← observeRead function.typedBody running initial .bool
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let argumentRead ← observeRead function.typedBody argument rhs .word
  let stopRead ← observeRead function.typedBody stop post .bool
  let finalRead ← observeRead function.typedBody value finalNode .word
  let ⟨valueScheme⟩ ← observed (value.scheme = .mono .word) "named for valueScheme"
  let ⟨valueRequirements⟩ ← observed (value.schemeRequirements = []) "named for valueRequirements"
  let ⟨valueOrdinary⟩ ← observed (value.comptime = false) "named for valueOrdinary"
  let ⟨valueOwner⟩ ← observed (value.id.owner = function.typedBody.owner) "named for valueOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named for argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named for argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named for argumentOrdinary"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "named for argumentOwner"
  let ⟨runningScheme⟩ ← observed (running.scheme = .mono .bool) "named for runningScheme"
  let ⟨runningRequirements⟩ ← observed (running.schemeRequirements = []) "named for runningRequirements"
  let ⟨runningOrdinary⟩ ← observed (running.comptime = false) "named for runningOrdinary"
  let ⟨runningOwner⟩ ← observed (running.id.owner = function.typedBody.owner) "named for runningOwner"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "named for stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "named for stopRequirements"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "named for stopOrdinary"
  let ⟨stopOwner⟩ ← observed (stop.id.owner = function.typedBody.owner) "named for stopOwner"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "named for flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "named for flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "named for flagOrdinary"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "named for flagOwner"
  let ⟨argumentValue⟩ ← observed (argument.id ≠ value.id) "named for argumentValue"
  let ⟨runningValue⟩ ← observed (running.id ≠ value.id) "named for runningValue"
  let ⟨runningArgument⟩ ← observed (running.id ≠ argument.id) "named for runningArgument"
  let ⟨stopValue⟩ ← observed (stop.id ≠ value.id) "named for stopValue"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "named for stopArgument"
  let ⟨stopRunning⟩ ← observed (stop.id ≠ running.id) "named for stopRunning"
  let ⟨flagValue⟩ ← observed (flag.id ≠ value.id) "named for flagValue"
  let ⟨flagArgument⟩ ← observed (flag.id ≠ argument.id) "named for flagArgument"
  let ⟨flagRunning⟩ ← observed (flag.id ≠ running.id) "named for flagRunning"
  let ⟨flagStop⟩ ← observed (flag.id ≠ stop.id) "named for flagStop"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named for parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word, .word, .bool, .bool]) "named for inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named for returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [value, argument, running, stop]) "named for inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named for roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named for assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "named for assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named for assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = value.id) "named for targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named for targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named for targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named for assignmentRequirements"
  let ⟨postRoot⟩ ← observed (postResolution.target.root = flag.id) "named for postRoot"
  let ⟨postType⟩ ← observed (postResolution.target.type = .bool) "named for postType"
  let ⟨postBare⟩ ← observed (postResolution.target.projections = []) "named for postBare"
  let ⟨postRequirements⟩ ← observed (postResolution.requirements = []) "named for postRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named for loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .forLoop [.letDecl flag (some initialRead.node.id)] conditionRead.node.id [.assignValue postResolution .equal stopRead.node.id] [assignment.id]) "named for loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named for loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named for statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named for statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named for statementType"
  return { value, argument, running, stop, flag, initialRead, conditionRead, argumentRead, stopRead, finalRead, assignment, resolution, postResolution, loop, statement, valueScheme, valueRequirements, valueOrdinary, valueOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentOwner, runningScheme, runningRequirements, runningOrdinary, runningOwner, stopScheme, stopRequirements, stopOrdinary, stopOwner, flagScheme, flagRequirements, flagOrdinary, flagOwner, argumentValue, runningValue, runningArgument, stopValue, stopArgument, stopRunning, flagValue, flagArgument, flagRunning, flagStop, parameters, inputTypes, returns, inputs, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, postRoot, postType, postBare, postRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named for graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named for methods")
    | _, _ => throw (IO.userError "named for declaration count")

end Tests.SourceCoreNamedFor
