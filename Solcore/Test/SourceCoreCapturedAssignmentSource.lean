import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
/-! Independent Source typing for a closure that returns its previous captured
Word and writes its argument into the same captured cell. -/
namespace Tests.SourceCoreCapturedAssignment
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
  previousRead : WordRead function.typedBody previous
  initialized : StatementNode
  assignment : StatementNode
  resolution : AssignmentResolution
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
  assignmentForm : assignment.form = .assignValue resolution .equal argumentRead.node.id
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
  lambda : expression.form = .lambda [argument] .word [initialized.id, assignment.id, innerReturn.id]
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
    have writable : WritableLocal locals shape.resolution.target.root .word := by
      rw [shape.targetRoot]
      exact .intro (.tail shape.previousDistinct (.tail shape.argumentDistinct head.local_self))
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible localWord)
        (by rw [scheme]; rfl) (by rw [scheme]; rfl)
    have assignmentTyped : SourceAssignmentHasType function.typedBody locals shape.resolution .equal shape.argumentRead.node.id :=
      .equal (.intro writable (by rw [shape.targetBare]; exact .nil _) shape.targetType) rhsTyped shape.assignmentRequirements
    have statementTyped : StatementHasType function.typedBody ⟨.word, 0⟩ locals shape.assignment.id locals ordinary :=
      .assignValue (lookupStatement?_sound shape.assignmentFound) shape.assignmentForm assignmentTyped shape.assignmentType
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
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(next: Word) { let previous: Word = seed; seed = next; return previous; }; }"}] }

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
  let [.expression initial, .statement initialized, .expression rhs, .statement assignment,
      .expression old, .statement innerReturn, .expression expression, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "assignment factory graph")
  let .lambda [argument] _ _ := expression.form | throw (IO.userError "lambda argument")
  let .letDecl previous _ := initialized.form | throw (IO.userError "previous binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "bare assignment")
  let initialRead ← observeRead function.typedBody binder initial
  let argumentRead ← observeRead function.typedBody argument rhs
  let previousRead ← observeRead function.typedBody previous old
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "assignment factory argumentScheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "assignment factory argumentRequirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "assignment factory argumentOwner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "assignment factory argumentDistinct"
  let ⟨previousScheme⟩ ← observed (previous.scheme = .mono .word) "assignment factory previousScheme"
  let ⟨previousRequirements⟩ ← observed (previous.schemeRequirements = []) "assignment factory previousRequirements"
  let ⟨previousOwner⟩ ← observed (previous.id.owner = function.typedBody.owner) "assignment factory previousOwner"
  let ⟨previousDistinct⟩ ← observed (previous.id ≠ binder.id) "assignment factory previousDistinct"
  let ⟨previousArgument⟩ ← observed (previous.id ≠ argument.id) "assignment factory previousArgument"
  let ⟨previousOrdinary⟩ ← observed (previous.comptime = false) "assignment factory previousOrdinary"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "assignment factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "assignment factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .word .word]) "assignment factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "assignment factory inputs"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "assignment factory binder owner"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "assignment factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "assignment factory roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "assignment factory initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl previous (some initialRead.node.id)) "assignment factory initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "assignment factory initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "assignment factory assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal argumentRead.node.id) "assignment factory assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "assignment factory assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = binder.id) "assignment factory targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = .word) "assignment factory targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "assignment factory targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "assignment factory assignmentRequirements"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "assignment factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "assignment factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "assignment factory statementFound"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some previousRead.node.id)) "assignment factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "assignment factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [argument] .word [initialized.id, assignment.id, innerReturn.id]) "assignment factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .word .word) "assignment factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .word .word) "assignment factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "assignment factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "assignment factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "assignment factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .word .word) "assignment factory statementType"
  return { binder, argument, previous, initialRead, argumentRead, previousRead, initialized, assignment, resolution, innerReturn, expression, statement, argumentScheme, argumentRequirements, argumentOwner, argumentDistinct, previousScheme, previousRequirements, previousOwner, previousDistinct, previousArgument, previousOrdinary, parameters, inputTypes, returns, inputs, binderOwner, binderRequirements, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, innerReturnFound, expressionFound, statementFound, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

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
    .expression sourceShape.argumentRead.node, .statement sourceShape.assignment,
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
          .expression sourceShape.argumentRead.node, .statement sourceShape.assignment,
          .expression sourceShape.previousRead.node, .statement sourceShape.innerReturn,
          .expression sourceShape.expression, .statement sourceShape.statement]) "complete assignment factory graph"
        return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
          function, signature, functions, signatures, methods, sourceShape, nodes⟩
      else throw (IO.userError "unexpected assignment factory methods")
    | _, _ => throw (IO.userError "assignment factory declaration count")

end Tests.SourceCoreCapturedAssignment
