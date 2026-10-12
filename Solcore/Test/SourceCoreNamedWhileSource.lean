import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Independent Source typing for a named function with a mutable while condition and an outer return. -/
namespace Tests.SourceCoreNamedWhile
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
  flag : TypedBinder
  argument : TypedBinder
  stop : TypedBinder
  conditionRead : BoolRead function.typedBody flag
  stopRead : BoolRead function.typedBody stop
  finalRead : WordRead function.typedBody argument
  assignment : StatementNode
  resolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  flagOrdinary : flag.comptime = false
  flagOwner : flag.id.owner = function.typedBody.owner
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOrdinary : argument.comptime = false
  argumentFlag : argument.id ≠ flag.id
  stopScheme : stop.scheme = .mono .bool
  stopRequirements : stop.schemeRequirements = []
  stopOrdinary : stop.comptime = false
  stopFlag : stop.id ≠ flag.id
  stopArgument : stop.id ≠ argument.id
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.bool, .word, .bool]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [flag, argument, stop]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal stopRead.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = flag.id
  targetType : resolution.target.type = .bool
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.stopRead.node,
    .statement shape.assignment, .statement shape.loop, .expression shape.finalRead.node, .statement shape.statement]

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
  | cons flagScheme flagExtended tail =>
    cases tail with
    | cons argumentScheme argumentExtended tail =>
      cases tail with
      | cons stopScheme stopExtended tail =>
        cases tail
        have binders : TypeParameterBindersWellFormed lexical := by
          rw [TypeParameterBindersWellFormed, stopExtended.context_fields.2.2.1,
            argumentExtended.context_fields.2.2.1, flagExtended.context_fields.2.2.1]
          simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
            Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
        have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
        have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
        have flagLookup : lexical.LocalLookup shape.flag.id shape.flag.scheme := by
          cases stopExtended
          cases argumentExtended
          exact .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_self)
        have flagRequirements : lexical.LocalSchemeRequirementsLookup shape.flag.id shape.flag.schemeRequirements := by
          cases stopExtended
          cases argumentExtended
          exact .tail shape.stopFlag (.tail shape.argumentFlag flagExtended.local_scheme_requirements_self)
        have conditionTyped := shape.conditionRead.typed flagScheme shape.flagRequirements bool flagLookup flagRequirements
        have rhsTyped := shape.stopRead.typed stopScheme shape.stopRequirements bool
          stopExtended.local_self stopExtended.local_scheme_requirements_self
        have finalTyped := shape.finalRead.typed argumentScheme shape.argumentRequirements word
          (by cases stopExtended; exact .tail shape.stopArgument argumentExtended.local_self)
          (by cases stopExtended; exact .tail shape.stopArgument argumentExtended.local_scheme_requirements_self)
        have writable : WritableLocal lexical shape.resolution.target.root .bool := by
          rw [shape.targetRoot]
          exact .intro flagLookup (flagScheme.symm ▸ SchemeWellFormed.monoAdmissible bool)
            (by rw [flagScheme]; rfl) (by rw [flagScheme]; rfl)
        have assignmentTyped : SourceAssignmentHasType function.typedBody lexical shape.resolution .equal shape.stopRead.node.id :=
          .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
        have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ lexical shape.assignment.id lexical ordinary :=
          .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
        have loopTyped := StatementHasType.whileLoop (control := ⟨.word, 0⟩)
          (lookupStatement?_sound shape.loopFound) shape.loopForm conditionTyped (.singleton assigned) shape.loopType
        have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
          (lookupStatement?_sound shape.statementFound) shape.statementForm finalTyped shape.statementType
        exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function choose(flag: Bool, value: Word, stop: Bool) returns (Word) { while (flag) { flag = stop; } return value; }"}] }

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
  let [flag, argument, stop] := function.typedBody.inputs | throw (IO.userError "named while inputs")
  let [.expression condition, .expression next, .statement assignment,
      .statement loop, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named while graph")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare flag assignment")
  let conditionRead ← observeRead function.typedBody flag condition .bool
  let stopRead ← observeRead function.typedBody stop next .bool
  let finalRead ← observeRead function.typedBody argument result .word
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "named while flagScheme"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "named while flagRequirements"
  let ⟨flagOrdinary⟩ ← observed (flag.comptime = false) "named while flagOrdinary"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "named while flagOwner"
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "named while argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "named while argumentRequirements"
  let ⟨argumentOrdinary⟩ ← observed (argument.comptime = false) "named while argumentOrdinary"
  let ⟨argumentFlag⟩ ← observed (argument.id ≠ flag.id) "named while argumentFlag"
  let ⟨stopScheme⟩ ← observed (stop.scheme = .mono .bool) "named while stopScheme"
  let ⟨stopRequirements⟩ ← observed (stop.schemeRequirements = []) "named while stopRequirements"
  let ⟨stopOrdinary⟩ ← observed (stop.comptime = false) "named while stopOrdinary"
  let ⟨stopFlag⟩ ← observed (stop.id ≠ flag.id) "named while stopFlag"
  let ⟨stopArgument⟩ ← observed (stop.id ≠ argument.id) "named while stopArgument"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named while parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.bool, .word, .bool]) "named while inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named while returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [flag, argument, stop]) "named while inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named while roots"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named while assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal stopRead.node.id) "named while assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named while assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = flag.id) "named while targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .bool) "named while targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named while targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named while assignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named while loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id]) "named while loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named while loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named while statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named while statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named while statementType"
  return { flag, argument, stop, conditionRead, stopRead, finalRead, assignment, resolution, loop, statement, flagScheme, flagRequirements, flagOrdinary, flagOwner, argumentScheme, argumentRequirements, argumentOrdinary, argumentFlag, stopScheme, stopRequirements, stopOrdinary, stopFlag, stopArgument, parameters, inputTypes, returns, inputs, roots, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named while graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named while methods")
    | _, _ => throw (IO.userError "named while declaration count")

end Tests.SourceCoreNamedWhile
