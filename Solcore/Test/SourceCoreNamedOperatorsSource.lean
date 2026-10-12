import Solcore.Test.SourceCoreNamedBranchSource
import Solcore.SourceSemantics.CoreLowering.NumericLiteralEvidenceReceipts
/-! Original checker receipts for primitive Word comparison and subtraction.
Literal requirements retain their actual builtin implementation evidence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedOperators
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read

private theorem builtin_word_evidence (context : SourceSemantics.Context) :
    RetainedEvidenceValid context.assumptions context.signatures.resolutionRules
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl (ProgramSignatures.builtinIntPredicate .word) (.builtin .intWord) [])) := by
  apply RetainedEvidenceValid.intro (.implementation (.byImpl .nil))
  exact .implementation (rule := ProgramSignatures.builtinIntWordRule) (by simp [ProgramSignatures.resolutionRules, ProgramSignatures.builtinResolutionRules]) rfl
    (.intro ⟨[], []⟩ ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩ rfl rfl) .nil

structure Literal (function : CheckedFunction) where
  node : ExpressionNode
  spelling : Syntax.CoreLiteralValue
  resolution : IntegerLiteralResolution
  validated : SourceCoreElaboration.WordIntegerLiteral
  found : function.typedBody.lookupExpression? node.id = some node
  form : node.form = .integerLiteral spelling resolution
  raw : node.rawType = .word
  accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution = .ok validated

theorem Literal.typed {function : CheckedFunction} (literal : Literal function)
    {context : SourceSemantics.Context} (word : TypeAdmissible context .word)
    (ledger : context.solvedRequirements = function.solvedRequirements) :
    ExpressionHasType function.typedBody context literal.node.id .word := by
  have metadata := SourceCoreElaboration.validateWordIntegerLiteral_sound literal.accepted
  obtain ⟨row, selected, predicate, evidence⟩ := CoreLowering.NumericLiteralEvidenceReceipts.word literal.accepted
  have member : row ∈ function.solvedRequirements.filter (fun row => decide (row.id = literal.resolution.requirement)) := by
    rw [selected]; simp
  obtain ⟨member, identity⟩ := List.mem_filter.mp member
  have proves : RequirementProves context literal.resolution.requirement
      (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) := by
    refine ⟨row, ⟨ledger ▸ member, of_decide_eq_true identity⟩, predicate, .intro ?_⟩
    rw [evidence, predicate]
    change RetainedEvidenceValid _ _ (ProgramSignatures.builtinIntPredicate literal.resolution.targetType) _
    rw [metadata.targetType]
    simpa only [IntegerLiteralResolution.predicate, metadata.targetType] using builtin_word_evidence context
  have valid : IntegerLiteralValid context literal.spelling literal.resolution :=
    .word metadata.meaning metadata.targetType proves
  have typed : ExpressionHasType function.typedBody context literal.node.id literal.node.type := by
    refine .intro (lookupExpression?_sound literal.found)
      (literal.form ▸ ExpressionFormHasRawType.integerLiteral valid)
      (literal.raw.trans metadata.targetType.symm) (metadata.targetType.symm ▸ word)
      (metadata.nodeType.symm ▸ word) ?_
    rw [metadata.requirements, metadata.coercions, metadata.targetType, metadata.nodeType]
    exact .ordinary (by intro id member; have same := List.mem_singleton.mp member; exact same ▸ valid.requirement_valid) (.nil _) rfl
  exact metadata.nodeType ▸ typed

structure Binary (source : TypedSource) (left right : ExpressionId)
    (operator : Syntax.BinaryOp) (result : TypeSystem.Ty) where
  node : ExpressionNode
  found : source.lookupExpression? node.id = some node
  form : node.form = .binary left operator right
  raw : node.rawType = result
  type : node.type = result
  requirements : node.requirements = []
  coercions : node.coercions = []

theorem Binary.typed {source : TypedSource} {left right : ExpressionId}
    {operator : Syntax.BinaryOp} {result : TypeSystem.Ty}
    (binary : Binary source left right operator result)
    {context : SourceSemantics.Context} (resultAdmissible : TypeAdmissible context result)
    (leftTyped : ExpressionHasType source context left .word)
    (rightTyped : ExpressionHasType source context right .word)
    (profile : BinaryOperatorHasType context operator .word .word result []) :
    ExpressionHasType source context binary.node.id result := by
  have typed : ExpressionHasType source context binary.node.id binary.node.type := by
    refine .intro (lookupExpression?_sound binary.found)
      (binary.form ▸ ExpressionFormHasRawType.binary leftTyped rightTyped profile)
      binary.raw resultAdmissible (binary.type.symm ▸ resultAdmissible) ?_
    rw [binary.requirements, binary.coercions, binary.type]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context binary.node.id type) binary.type) typed

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  conditionRead : Read function.typedBody binder .word
  zero : Literal function
  comparison : Binary function.typedBody conditionRead.node.id zero.node.id .greater .bool
  argumentRead : Read function.typedBody binder .word
  one : Literal function
  difference : Binary function.typedBody argumentRead.node.id one.node.id .subtract .word
  finalRead : Read function.typedBody binder .word
  assignment : StatementNode
  resolution : AssignmentResolution
  loop : StatementNode
  statement : StatementNode
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  binderOwner : binder.id.owner = function.typedBody.owner
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  roots : function.typedBody.roots = [.statement loop.id, .statement statement.id]
  zeroValue : zero.resolution.rawValue = 0
  oneValue : one.resolution.rawValue = 1
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal difference.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = binder.id
  targetType : resolution.target.type = .word
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop comparison.node.id [assignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalRead.node.id)
  statementType : statement.type = .word

def FactoryShape.body {function signature} (shape : FactoryShape function signature) : List StatementId :=
  [shape.loop.id, shape.statement.id]

def FactoryShape.nodeList {function signature} (shape : FactoryShape function signature) : List SourceInference.Node :=
  [.expression shape.conditionRead.node, .expression shape.zero.node, .expression shape.comparison.node,
    .expression shape.argumentRead.node, .expression shape.one.node, .expression shape.difference.node,
    .statement shape.assignment, .statement shape.loop,
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
  | cons binderScheme binderExtended tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, binderExtended.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have bool : TypeAdmissible lexical .bool := ⟨binders, .builtin .bool⟩
    have ledger : lexical.solvedRequirements = function.solvedRequirements := by cases binderExtended; rfl
    have conditionRead := shape.conditionRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have argumentRead := shape.argumentRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have finalRead := shape.finalRead.typed binderScheme shape.binderRequirements word
      binderExtended.local_self binderExtended.local_scheme_requirements_self
    have comparison := shape.comparison.typed bool conditionRead (shape.zero.typed word ledger) (.wordComparison .greater)
    have difference := shape.difference.typed word argumentRead (shape.one.typed word ledger) (.wordArithmetic .subtract)
    have writable : WritableLocal lexical shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro binderExtended.local_self (binderScheme.symm ▸ SchemeWellFormed.monoAdmissible word)
        (by rw [binderScheme]; rfl) (by rw [binderScheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody lexical shape.resolution .equal shape.difference.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) difference shape.assignmentRequirements
    have assigned : StatementHasType function.typedBody ⟨.word, 1⟩ lexical shape.assignment.id lexical ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
    have loopTyped := StatementHasType.whileLoop (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.loopFound) shape.loopForm comparison (.singleton assigned) shape.loopType
    have returned := StatementHasType.returnValue (control := ⟨.word, 0⟩)
      (lookupStatement?_sound shape.statementFound) shape.statementForm finalRead shape.statementType
    exact ⟨lexical, .cons loopTyped (.singleton returned)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function drain(n: Word) returns (Word) { while (n > 0) { n = n - 1; } return n; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeRead (source : TypedSource) (binder : TypedBinder) (node : ExpressionNode) : IO (Read source binder .word) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "read lookup"
  let ⟨form⟩ ← observed (node.form = .reference binder.name (.local binder.id)) "read binder"
  let ⟨raw⟩ ← observed (node.rawType = .word) "read raw Word"
  let ⟨type⟩ ← observed (node.type = .word) "read Word"
  let ⟨requirements⟩ ← observed (node.requirements = []) "read requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "read coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeLiteral (function : CheckedFunction) (node : ExpressionNode) : IO (Literal function) := do
  match form : node.form with
  | .integerLiteral spelling resolution =>
    match accepted : SourceCoreElaboration.validateWordIntegerLiteral function.solvedRequirements node spelling resolution with
    | .error error => throw (IO.userError (reprStr error))
    | .ok validated =>
      let ⟨found⟩ ← observed (function.typedBody.lookupExpression? node.id = some node) "literal lookup"
      let ⟨raw⟩ ← observed (node.rawType = .word) "literal raw Word"
      return ⟨node, spelling, resolution, validated, found, form, raw, accepted⟩
  | _ => throw (IO.userError "integer literal expected")

def observeBinary (source : TypedSource) (left right : ExpressionId) (operator : Syntax.BinaryOp)
    (result : TypeSystem.Ty) (node : ExpressionNode) : IO (Binary source left right operator result) := do
  let ⟨found⟩ ← observed (source.lookupExpression? node.id = some node) "binary lookup"
  let ⟨form⟩ ← observed (node.form = .binary left operator right) "binary operation"
  let ⟨raw⟩ ← observed (node.rawType = result) "binary raw type"
  let ⟨type⟩ ← observed (node.type = result) "binary type"
  let ⟨requirements⟩ ← observed (node.requirements = []) "primitive binary requirements"
  let ⟨coercions⟩ ← observed (node.coercions = []) "primitive binary coercions"
  return { node, found, form, raw, type, requirements, coercions }

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "named operator inputs")
  let [.expression condition, .expression zeroNode, .expression compareNode,
      .expression argument, .expression oneNode, .expression subtractNode,
      .statement assignment, .statement loop, .expression result, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "named operator graph")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare Word assignment")
  let conditionRead ← observeRead function.typedBody binder condition
  let zero ← observeLiteral function zeroNode
  let comparison ← observeBinary function.typedBody conditionRead.node.id zero.node.id .greater .bool compareNode
  let argumentRead ← observeRead function.typedBody binder argument
  let one ← observeLiteral function oneNode
  let difference ← observeBinary function.typedBody argumentRead.node.id one.node.id .subtract .word subtractNode
  let finalRead ← observeRead function.typedBody binder result
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "named operator binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "named operator binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "named operator binderOrdinary"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "named operator binderOwner"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "named operator parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "named operator inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "named operator returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "named operator inputs"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement loop.id, .statement statement.id]) "named operator roots"
  let ⟨zeroValue⟩ ← observed (zero.resolution.rawValue = 0) "named operator zeroValue"
  let ⟨oneValue⟩ ← observed (one.resolution.rawValue = 1) "named operator oneValue"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "named operator assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal difference.node.id) "named operator assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "named operator assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "named operator targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "named operator targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "named operator targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "named operator assignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "named operator loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop comparison.node.id [assignment.id]) "named operator loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "named operator loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "named operator statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalRead.node.id)) "named operator statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "named operator statementType"
  return { binder, conditionRead, zero, comparison, argumentRead, one, difference, finalRead, assignment, resolution, loop, statement, binderScheme, binderRequirements, binderOrdinary, binderOwner, parameters, inputTypes, returns, inputs, roots, zeroValue, oneValue, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType }

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
        let ⟨nodes⟩ ← observed (function.typedBody.nodes = sourceShape.nodeList) "complete named operators graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected named operators methods")
    | _, _ => throw (IO.userError "named operators declaration count")

end Tests.SourceCoreNamedOperators
