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
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.AcceptedPackets
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.OrdinarySequenceCallers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots

/-!
# Captured closure assignment tests

Closures with mutable captures, copied captures and packed captures.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentSource
/-! Independent Source typing for a closure that returns its previous captured
Word and writes its argument into the same captured cell. -/

set_option autoImplicit false
set_option Elab.async false

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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentFixture
/-! Actual compilation, selected inventory and static lambda observations for
one mutable captured Word closure with one Word argument. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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
    .expression shape.argumentRead.node, .statement shape.assignment,
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
          .expression shape.argumentRead.node, .statement shape.assignment,
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
      body = [observed.shape.initialized.id, observed.shape.assignment.id, observed.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  have alternatives : node = observed.shape.initialRead.node ∨ node = observed.shape.argumentRead.node ∨
      node = observed.shape.previousRead.node ∨ node = observed.expression := by simpa using member
  rcases alternatives with rfl | rfl | rfl | rfl
  · rw [observed.shape.initialRead.form] at form; cases form
  · rw [observed.shape.argumentRead.form] at form; cases form
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


end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentMetadata
/-! The actual eight-node source supplies original policy metadata for all three original local reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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
      node = observed.shape.previousRead.node ∨ node = observed.shape.expression := by simpa using present
  rcases alternatives with rfl | rfl | rfl | rfl
  · exact .inl ⟨_, _, observed.shape.initialRead.form,
      observed.shape.initialRead.requirements, observed.shape.initialRead.coercions⟩
  · exact .inl ⟨_, _, observed.shape.argumentRead.form,
      observed.shape.argumentRead.requirements, observed.shape.argumentRead.coercions⟩
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

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentRuntime
/-! Actual public calls retain each returned session and opaque handle.
Captures are by value: every call starts again from the seed its closure
captured, so a call's write reaches neither the next call nor another closure. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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
    | .ok (.failed _ _) => throw (IO.userError "assignment factory call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "assignment factory call exhausted")
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "assignment factory result was not a function")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedPublicRun fixture observed
  second : ObservedFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
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
  else throw (IO.userError "assignment returned wrong previous value")

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let second ← observeFunctionCall first.completion.session observed.row.key [.word (Core.Word.ofNatModulo 20)]
  let firstCall ← observeInvocation second.completion.session first.handle (Core.Word.ofNatModulo 11)
  let ⟨firstValue⟩ ← observeWord firstCall.completion (Core.Word.ofNatModulo 10)
  let third ← observeFunctionCall firstCall.completion.session observed.row.key [.word (Core.Word.ofNatModulo 30)]
  let secondCall ← observeInvocation third.completion.session second.handle (Core.Word.ofNatModulo 21)
  let ⟨secondValue⟩ ← observeWord secondCall.completion (Core.Word.ofNatModulo 20)
  let firstAgain ← observeInvocation secondCall.completion.session first.handle (Core.Word.ofNatModulo 12)
  let ⟨finalValue⟩ ← observeWord firstAgain.completion (Core.Word.ofNatModulo 10)
  return ⟨first, second, firstCall, firstValue, third, secondCall, secondValue, firstAgain, finalValue⟩

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentSyntax
/-! Original Source typing determines the lexical extension, writable captured
cell and ordered read children of the real mutable closure body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedAssignment
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.previousOwner, Ne.symm observed.shape.previousDistinct,
    Ne.symm observed.shape.previousArgument, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape observed.row.function.typedBody
      [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] :=
  .initialized observed.shape.initializedFound observed.shape.initializedForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare
      (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm))

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    {approved : ExpressionId → Prop}
    (initializerApproved : approved observed.shape.initialRead.node.id)
    (argumentApproved : approved observed.shape.argumentRead.node.id)
    (previousApproved : approved observed.shape.previousRead.node.id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id]) .word := by
  have declaration := observed.previous_declaration
  have seed := observed.seed_declaration
  have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.shape.previous.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.previousDistinct]
  cases typed with
  | cons head tail =>
    cases tail with
    | cons assigned tail =>
      cases tail with
      | singleton last =>
        cases head with
        | letInitialized contains form initializer monoActual generalized extended type =>
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
            initializerApproved
          cases assigned with
          | assignValue contains form typedAssignment type =>
            have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.assignmentFound)
            cases same
            rw [observed.shape.assignmentForm] at form
            obtain ⟨sameAssignment, sameOperator, sameRhs⟩ := StatementForm.assignValue.inj form
            cases sameAssignment
            cases sameOperator
            cases sameRhs
            cases typedAssignment with
            | wordCompound operator _ _ _ => cases operator
            | equal target rhs requirements =>
              cases target with
              | intro writable projections targetType =>
                have rootFound : SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.resolution.target.root =
                    .ok observed.shape.binder := by rw [observed.shape.targetRoot]; exact seed
                apply GenericImperativeMatch.Syntax.assign observed.shape.assignmentFound observed.shape.assignmentForm
                · intro binder found
                  have equal := Except.ok.inj (rootFound.symm.trans found)
                  cases equal
                  rw [observed.binderScheme, observed.shape.targetBare, observed.shape.targetType]
                  exact .nil _
                · intro binder found
                  have equal := Except.ok.inj (rootFound.symm.trans found)
                  cases equal
                  rw [observed.shape.targetBare] at projections
                  cases projections
                  have word := targetType.symm.trans observed.shape.targetType
                  simpa only [word, observed.binderScheme, TypeSystem.Scheme.mono] using writable
                · simpa only [targetType] using rhs
                · exact .inl rfl
                · intro id member
                  simp only [observed.shape.targetBare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
                  cases member
                  exact ⟨argumentApproved, observed.shape.argumentRead.node, observed.shape.argumentRead.found,
                    by simpa only [← targetType, observed.shape.targetType, observed.shape.argumentRead.type] using rhs⟩
                · apply GenericImperativeMatch.Syntax.body
                  cases last with
                  | returnValue contains form expression type =>
                    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.innerReturnFound)
                    cases same
                    rw [observed.shape.innerReturnForm] at form
                    cases Option.some.inj (StatementForm.returnStmt.inj form)
                    exact .returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm type
                      observed.shape.previousRead.found observed.shape.previousRead.type
                      (by simpa only [observed.shape.previousRead.type] using expression) previousApproved
                  | _ =>
                    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.innerReturnFound)
                    cases same
                    simp_all [observed.shape.innerReturnForm]
          | _ =>
            have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.assignmentFound)
            cases same
            simp_all [observed.shape.assignmentForm]
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
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody) context
      (.statements true [observed.shape.initialized.id, observed.shape.assignment.id, observed.shape.innerReturn.id]) .word :=
  observed.body_syntax unique
    ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
    ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
    ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩ typed

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentSupports
/-! A complete singleton inventory supplies formation and every authentic
captured-read closure body, including the actual nonempty parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedImperativeBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
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
    exact observed.body_syntax (actual.source ▸ actual.header.unique) True.intro True.intro True.intro typed


theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression
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
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function .word .word := by
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
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point (registry := registry) (faults := faults)
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
      have shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape function.source function.body := by
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
      exact CallableIndexedOwnedPreparedStagedImperativeLambdaReadRoots.of_reads code support provenance receiver
        fixture.source_wellFormed (by rw [sameSource]; exact observed.metadata support.caller.named)
        shape syntaxTree (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports, family := family, descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentCommon
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted nonzero-parameter factory; retained states refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentInvocation
/-! Actual one-Word public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedAssignment
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
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .word (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
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

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedAssignment
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
  · change request.header.function.resultType = .function .word .word
    rw [selected]
    exact support.actual.result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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


end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedAssignmentPublicExecution
/-! The first closure is called again after a separate closure and a fresh
factory allocation, and its second call starts again from its captured seed:
the write of its first call does not carry over. Every transition uses the
actual returned public session and the same Source heap retained by the
previous call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
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
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle,
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
  IO.println "Actual captured assignment: make10/make20, first11 returns10, make30, second21 returns20, first12 returns10; six Source calls and returned histories proved"

end Tests.SourceCoreCapturedAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopySource
/-! Independent Source typing for a factory whose returned closure initializes a fresh
lexical local from its captured parameter on each invocation. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  localBinder : TypedBinder
  localScheme : localBinder.scheme = .mono .word
  localRequirements : localBinder.schemeRequirements = []
  localOrdinary : localBinder.comptime = false
  localOwner : localBinder.id.owner = function.typedBody.owner
  localDistinct : localBinder.id ≠ binder.id
  initialRead : ExpressionNode
  initialized : StatementNode
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .unit .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  initialReadFound : function.typedBody.lookupExpression? initialRead.id = some initialRead
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initialReadForm : initialRead.form = .reference binder.name (.local binder.id)
  initialReadRaw : initialRead.rawType = .word
  initialReadType : initialRead.type = .word
  initialReadRequirements : initialRead.requirements = []
  initialReadCoercions : initialRead.coercions = []
  initializedForm : initialized.form = .letDecl localBinder (some initialRead.id)
  initializedType : initialized.type = .unit
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference localBinder.name (.local localBinder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerReturnForm : innerReturn.form = .returnStmt (some read.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [] .word [initialized.id, innerReturn.id]
  expressionRaw : expression.rawType = .function .unit .word
  expressionType : expression.type = .function .unit .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .word

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
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .word
    hasValue := true
    sawReturn := true
    control := .returned }
  let letFacts : StatementFacts := {
    type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    let innerContext := lexical.withLocal shape.localBinder.id shape.localBinder.scheme shape.localBinder.schemeRequirements
    have localExtended : BinderExtends function.typedBody.owner lexical shape.localBinder innerContext := by
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
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have innerWord : TypeAdmissible innerContext .word := ⟨binders, .builtin .word⟩
    have initialInstantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have initialReadTyped : ExpressionHasType function.typedBody lexical shape.initialRead.id .word := by
      rw [← shape.initialReadType]
      refine .intro (lookupExpression?_sound shape.initialReadFound)
        (shape.initialReadForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self initialInstantiation))
        shape.initialReadRaw word (shape.initialReadType ▸ word) ?_
      rw [shape.initialReadRequirements, shape.initialReadCoercions, shape.initialReadType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have instantiation : LocalSchemeInstantiationValid innerContext shape.localBinder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.localRequirements)
        (shape.localScheme.symm ▸ SchemeWellFormed.monoAdmissible innerWord) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.localRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody innerContext shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local localExtended.local_self localExtended.local_scheme_requirements_self instantiation))
        shape.readRaw innerWord (shape.readType ▸ innerWord) ?_
      rw [shape.readRequirements, shape.readCoercions, shape.readType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initializedTyped : StatementHasType function.typedBody
        ⟨.word, 0⟩ lexical shape.initialized.id innerContext letFacts := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initialReadTyped
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp)
          (.nil _)
          (.cons initializedTyped (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType)))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { return lam() { let copy: Word = seed; return copy; }; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression initialRead, Node.statement initialized, Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let .letDecl localBinder _ := initialized.form
    | throw (IO.userError "captured local binder")
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "closure local scheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "closure local requirements"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "captured local ordinary binder"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "closure local owner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "closure local identity"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured factory roots"
  let ⟨initialReadFound⟩ ← observed (function.typedBody.lookupExpression? initialRead.id = some initialRead) "captured local initialReadFound"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "captured local initializedFound"
  let ⟨initialReadForm⟩ ← observed (initialRead.form = .reference binder.name (.local binder.id)) "captured local initialReadForm"
  let ⟨initialReadRaw⟩ ← observed (initialRead.rawType = .word) "captured local initialReadRaw"
  let ⟨initialReadType⟩ ← observed (initialRead.type = .word) "captured local initialReadType"
  let ⟨initialReadRequirements⟩ ← observed (initialRead.requirements = []) "captured local initialReadRequirements"
  let ⟨initialReadCoercions⟩ ← observed (initialRead.coercions = []) "captured local initialReadCoercions"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some initialRead.id)) "captured local initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "captured local initializedType"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference localBinder.name (.local localBinder.id)) "captured factory readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "captured factory readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "captured factory readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured factory readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured factory readCoercions"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some read.id)) "captured factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [initialized.id, innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .unit .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .unit .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "captured factory statementType"
  return { binder, localBinder, localScheme, localRequirements, localOrdinary, localOwner, localDistinct, initialRead, initialized, initialReadFound, initializedFound, initialReadForm, initialReadRaw, initialReadType, initialReadRequirements, initialReadCoercions, initializedForm, initializedType, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

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
  nodes : function.typedBody.nodes = [.expression sourceShape.initialRead, .statement sourceShape.initialized, .expression sourceShape.read,
    .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement]

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
        if nodes : function.typedBody.nodes = [.expression sourceShape.initialRead, .statement sourceShape.initialized, .expression sourceShape.read,
            .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement] then
          return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
            function, signature, functions, signatures, methods, sourceShape, nodes⟩
        else throw (IO.userError "captured factory complete node graph changed")
      else throw (IO.userError "unexpected captured factory methods")
    | _, _ => throw (IO.userError "captured factory declaration count")

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyFixture
/-! Actual compilation, selected inventory and static lambda observations for
a closure that initializes its own local from a captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
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

structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  shape : FactoryShape row.function fixture.signature
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = fixture.signature.id
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  resultType : row.function.inferredBodyType = .function .unit .word
  binderOrdinary : shape.binder.comptime = false
  binderScheme : shape.binder.scheme = .mono .word
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  nodes : row.function.typedBody.nodes = [.expression shape.initialRead, .statement shape.initialized, .expression shape.read, .statement shape.innerReturn,
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
abbrev ObservedFactory.localBinder {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.localBinder
abbrev ObservedFactory.localScheme {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.localScheme
abbrev ObservedFactory.innerReturn {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturn
abbrev ObservedFactory.expression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expression
abbrev ObservedFactory.statement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statement
abbrev ObservedFactory.inputs {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.inputs
abbrev ObservedFactory.roots {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.roots
abbrev ObservedFactory.lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.lambda
abbrev ObservedFactory.requirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.requirements
abbrev ObservedFactory.coercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.coercions
abbrev ObservedFactory.readForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readForm
abbrev ObservedFactory.readRaw {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readRaw
abbrev ObservedFactory.readType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readType
abbrev ObservedFactory.readRequirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readRequirements
abbrev ObservedFactory.readCoercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readCoercions
abbrev ObservedFactory.innerReturnForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnForm
abbrev ObservedFactory.innerReturnType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnType
abbrev ObservedFactory.returnStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.returnStatement
abbrev ObservedFactory.bodyRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.read
abbrev ObservedFactory.foundStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statementFound
abbrev ObservedFactory.foundExpression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expressionFound
abbrev ObservedFactory.foundRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readFound
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
        let ⟨same⟩ ← observeFact (node = shape.expression) "local factory reader"
        let ⟨sourceOwner⟩ ← observeFact (row.function.typedBody.owner = fixture.signature.id) "local source owner"
        let ⟨parameters⟩ ← observeFact (row.parameterSubstitution = []) "local substitution"
        let ⟨closed⟩ ← observeFact (row.assumptions = []) "local assumptions"
        let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .function .unit .word) "local factory output type"
        let ⟨ordinary⟩ ← observeFact (row.function.returnComptime = false) "local ordinary result"
        let ⟨binderOrdinary⟩ ← observeFact (shape.binder.comptime = false) "local seed ordinary"
        let ⟨binderScheme⟩ ← observeFact (shape.binder.scheme = .mono .word) "local seed type"
        let ⟨target⟩ ← observeTarget fixture row
        let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = [.expression shape.initialRead, .statement shape.initialized, .expression shape.read,
          .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]) "local nodes"
        let ⟨owned⟩ ← observeFact (shape.expression.id.occurrence.owner = row.function.typedBody.owner) "local lambda owner"
        let ⟨noLocals⟩ ← observeFact (fixture.recipe.compiled.indexed.base.locals.bindings = []) "local local catalog"
        let ⟨profile⟩ ← observeFact (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "local profile"
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
    | _ => throw (IO.userError "local factory entry count")
  | _ => throw (IO.userError "local factory specialization count")

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
    parameters = [] ∧ result = .word ∧ body = [observed.shape.initialized.id, observed.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  rcases List.mem_cons.mp member with initial | rest
  · have nodeEq := Node.expression.inj initial
    rw [nodeEq, observed.shape.initialReadForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | member
    · cases impossible
    ·
      rcases List.mem_cons.mp member with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.readForm] at form
        cases form
      · rcases List.mem_cons.mp rest with impossible | rest
        · cases impossible
        · rcases List.mem_cons.mp rest with same | rest
          · have nodeEq := Node.expression.inj same
            rw [nodeEq, observed.lambda] at form
            obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
            exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
          · rcases List.mem_cons.mp rest with impossible | empty
            · cases impossible
            · cases empty

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


end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyMetadata
/-! The actual six-node source supplies original policy metadata for both the
initializer's seed read and the closure body's distinct captured-local read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedReadLambdaMetadata (NodeMetadata)

theorem ObservedFactory.node_metadata {fixture : CompiledFixture}
    (observed : ObservedFactory fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    NodeMetadata node := by
  have present := (lookupExpression?_sound found).1
  rw [observed.nodes] at present
  have alternatives : node = observed.shape.initialRead ∨ node = observed.shape.read ∨
      node = observed.shape.expression := by simpa using present
  rcases alternatives with rfl | rfl | rfl
  · exact .inl ⟨_, _, observed.shape.initialReadForm,
      observed.shape.initialReadRequirements, observed.shape.initialReadCoercions⟩
  · exact .inl ⟨_, _, observed.shape.readForm,
      observed.shape.readRequirements, observed.shape.readCoercions⟩
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

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyRuntime
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this factory with lexical closure bodies; receipts refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

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


end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopySequence
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
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
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle .unit runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedInvocation session handle) := do
  match started : session.startHandlePacked handle .unit runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.invokePackedWithReceipt handle .unit runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "direct captured call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "direct captured call exhausted")
    | .ok (.succeeded completion) =>
      return ⟨checkpoint, started, completion, result ▸ executed.property⟩

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedPublicRun fixture observed
  second : ObservedFunctionCall first.completion.session observed.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  invokeFirst : ObservedInvocation second.completion.session first.handle
  firstValue : invokeFirst.completion.value = .word seed
  intervening : ObservedFunctionCall invokeFirst.completion.session observed.row.key [.word interveningSeed]
  invokeSecond : ObservedInvocation intervening.completion.session second.handle
  secondValue : invokeSecond.completion.value = .word secondSeed
  invokeFirstAgain : ObservedInvocation invokeSecond.completion.session first.handle
  firstValueAgain : invokeFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let second ← observeFunctionCall first.completion.session observed.row.key [.word secondSeed]
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "distinct direct closures reused the same handle"
  let invokeFirst ← observeInvocation second.completion.session first.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "first direct capture did not return 10"
  let intervening ← observeFunctionCall invokeFirst.completion.session observed.row.key [.word interveningSeed]
  let invokeSecond ← observeInvocation intervening.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "second direct capture did not return 20"
  let invokeFirstAgain ← observeInvocation invokeSecond.completion.session first.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "first direct capture changed after intervening calls"
  pure ⟨first, second, distinct, invokeFirst, firstValue, intervening, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopySyntax
/-! The actual Source typing provides the lexical extension and both child
judgments for the accepted initializer/return body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.localBinder.id = .ok observed.localBinder := by
  have distinct : observed.binder.id ≠ observed.localBinder.id := Ne.symm observed.shape.localDistinct
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialReadForm, observed.shape.initializedForm,
    observed.readForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.localOwner, distinct, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    {approved : ExpressionId → Prop}
    (initializerApproved : approved observed.shape.initialRead.id)
    (readApproved : approved observed.bodyRead.id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.initialized.id, observed.innerReturn.id] final facts) :
    GenericLexicalStatements.Syntax observed.row.function.typedBody approved
      context true [observed.shape.initialized.id, observed.innerReturn.id] .word := by
  have declaration := observed.local_declaration
  have mono : observed.localBinder.scheme.quantified = [] := by rw [observed.localScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.localBinder.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.localDistinct]
  cases typed with
  | cons head tail =>
    cases tail with
    | singleton last =>
      cases head with
      | letInitialized contains form initializer monoActual generalized extended type =>
        have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
        cases same
        rw [observed.shape.initializedForm] at form
        obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
        cases sameBinder
        cases Option.some.inj sameInitializer
        apply GenericLexicalStatements.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
          declaration mono extended ordinary observed.shape.initialReadFound
          (by rw [observed.shape.initialReadType, observed.localScheme]; rfl)
          (by simpa only [observed.shape.initialReadType, observed.localScheme, TypeSystem.Scheme.mono] using initializer)
          initializerApproved
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.foundInnerReturn)
          cases same
          rw [observed.innerReturnForm] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.foundInnerReturn observed.innerReturnForm type
            observed.foundRead
            observed.readType
            (by simpa only [observed.readType] using expression)
            readApproved
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.foundInnerReturn)
          cases same
          simp_all [observed.innerReturnForm]
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
        simp_all [observed.shape.initializedForm, observed.localScheme, TypeSystem.Scheme.mono]

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyClosureFamily
/-! Every authentic returned closure of this compiled program receives the
actual lexical body certificate. Its initializer reads the captured seed, then
the returned expression reads the newly allocated local cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def ActualHeader.closure_family {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor
      (actualStagePrepared fixture) association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    apply CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.SupportFor.of_generic_packets
    have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
    have found := code.sourceFound
    rw [sameSource] at found
    have shape := observed.lambda_shape found code.sourceForm
    have bodyShape := shape.2.2
    have resultShape := shape.2.1
    have treeShape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body := by
      rw [sameSource, bodyShape]
      exact .initialized observed.shape.initializedFound observed.shape.initializedForm
        (.returnValue [] observed.foundInnerReturn observed.innerReturnForm)
    obtain ⟨finalContext, bodyFacts, typed, _complete⟩ :=
      CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters support.body.frame support.body.extended
    have syntaxTree : GenericLexicalStatements.Syntax function.source
        (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read function.source)
        support.body.context true function.body function.resultType := by
      rw [sameSource, bodyShape, resultShape] at typed ⊢
      apply observed.body_syntax (by rw [← sameSource]; exact support.unique) ?_ ?_ typed
      · exact ⟨observed.shape.initialRead, _, _, observed.shape.initialReadFound, observed.shape.initialReadForm⟩
      · exact ⟨observed.bodyRead, _, _, observed.foundRead, observed.readForm⟩
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
    exact CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.of_reads code support provenance
      receiver fixture.source_wellFormed (by rw [sameSource]; exact observed.metadata support.caller.named)
      treeShape syntaxTree (RecursiveStageRegistry.scope sidecar code.active function)
      (RecursiveNamedPreparedStageScopes.anonymous_preserved (actualStagePrepared fixture) selected)

  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyTypes
set_option autoImplicit false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.input_types {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.result_type {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function .unit .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.resultType

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopySupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

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


theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedLexicalBodyLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.entryMember
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read
  · intro context final facts typed
    rw [actual.source] at typed ⊢
    exact observed.body_syntax (actual.source ▸ actual.header.unique) True.intro True.intro typed

theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩


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
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named actual.header.named.signature.key)

 theorem StaticSupportPackage.header_list {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) : headers support.rows = [support.actual.header] := by
  rw [support.rowsEq, support.headerEq]
  rfl

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
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point (registry := registry) (faults := faults)
  let terminals : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedStagedNamedBodies.Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal
  have supports : ∀ header (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows),
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (terminals header member) faults := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, ObservedStages.registry, stagePrepared,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support,
      CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal] using support
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports, family := fun association => actual.closure_family stages receiver association, descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyCommon
/-! Source calls and retained histories use the same actual returned public
sessions for the factory and subsequent closure invocations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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


end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
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
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
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

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyInvocation
/-! Actual nullary public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine zero arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [] outcome after

/-- Both the packed argument and callee meaning come from the original encoder
and current History. The returned state uses this call's exact public completion. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
    (parameters : function.parameters = [])
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function .unit .word)
    (call : ObservedInvocation publicSession handle)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source (.value (.word word)) after.heap := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .unit .unit .unit :=
    .data ⟨.unit, (by simp [SourceCoreIndexedSession.DataInput.publicValue]), .unit⟩
      ⟨.unit, (by simp [SourceCoreIndexedSession.DataInput.publicValue]), .unit⟩
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
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (history := state.history)
      (entry := entry) (member := member) (entryType := entryType) (entrySource := entrySource)
      (input := input) (atRecipe := state.atRecipe)
      state.registry receiver.completion.result.extension (.simple .unit)
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function .unit .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [] :=
    packing.injective_of_length_eq .nil (by simpa [parameters] using arity)
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, sourcesEq, outcomeValue] using trace

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedCopy
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
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.actual.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.actual.header := by
    exact List.mem_singleton.mp (support.header_list ▸ request.selected.member)
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
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
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
  · change request.header.function.resultType = .function .unit .word
    rw [selected]
    exact support.actual.result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopySeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed)
    (first : ObservedPublicRun fixture observed) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.actual.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
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
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
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


end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedCopyPublicExecution
/-! Three actual factory executions and three direct public handle invocations
retain distinct captures through intervening calls, with independent Source
applications and exact returned histories for the complete sequence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (makeStages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.actual.header.function
    ∃ first second intervening : Entry,
      first.sourceType = .function .unit .word ∧ second.sourceType = .function .unit .word ∧
      intervening.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ second.handle = sequence.second.handle ∧
      intervening.handle = sequence.intervening.handle ∧ first.handle ≠ second.handle ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, second],
      ∃ firstInvokedState : RetainedState support sequence.invokeFirst.completion.session [first, second],
      ∃ interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening],
      ∃ secondInvokedState : RetainedState support sequence.invokeSecond.completion.session [first, second, intervening],
      ∃ finalState : RetainedState support sequence.invokeFirstAgain.completion.session [first, second, intervening],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.actual.header scope firstState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        SourceInvocation support scope secondState.heap first.source
          (.value (.word seed)) firstInvokedState.heap ∧
        SourceCall support support.actual.header scope firstInvokedState.heap [.word interveningSeed]
          (.value intervening.source) interveningState.heap ∧
        SourceInvocation support scope interveningState.heap second.source
          (.value (.word secondSeed)) secondInvokedState.heap ∧
        SourceInvocation support scope secondInvokedState.heap first.source
          (.value (.word seed)) finalState.heap

/-- Every initial state, callable, capture, argument and result belongs to the
original actual public execution; semantic body laws are constructed internally. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (makeStages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed makeStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.actual.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, firstState, firstTrace⟩ :=
    first_meaning support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    firstState.make_typed_handle sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨firstInvokedState, firstInvokedTrace⟩ := invoke secondState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirst sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstInvokedState.make_typed_handle sequence.intervening scope
  obtain ⟨secondInvokedState, secondInvokedTrace⟩ := invoke interveningState second (by simp)
    secondType secondSource secondParameters secondHandle secondHandleType sequence.invokeSecond sequence.secondValue scope
  obtain ⟨finalState, finalTrace⟩ := invoke secondInvokedState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirstAgain sequence.firstValueAgain scope
  refine ⟨support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, ?_, firstState, secondState, firstInvokedState,
    interveningState, secondInvokedState, finalState, firstTrace, secondTrace, firstInvokedTrace,
    interveningTrace, secondInvokedTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let makeStages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed makeStages sequence receiver
  IO.println "Actual closure body local: six public calls, independent captures 10/20, intervening make(30), Source results and returned histories proved"

end Tests.SourceCoreCapturedCopy
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedSource
/-! Independent Source typing for the actual captured Word factory with one
Word argument. The body reads the outer seed after the new argument is installed;
its stable binder identity and original lexical lookup remain explicit. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  argument : TypedBinder
  argumentScheme : argument.scheme = .mono .word
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentDistinct : argument.id ≠ binder.id
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function .word .word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  readFound : function.typedBody.lookupExpression? read.id = some read
  innerReturnFound : function.typedBody.lookupStatement? innerReturn.id = some innerReturn
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  innerReturnForm : innerReturn.form = .returnStmt (some read.id)
  innerReturnType : innerReturn.type = .word
  lambda : expression.form = .lambda [argument] .word [innerReturn.id]
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
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .word .word
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons scheme head tail =>
    cases tail
    have binders : TypeParameterBindersWellFormed lexical := by
      rw [TypeParameterBindersWellFormed, head.context_fields.2.2.1]
      simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
        Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables,
        shape.parameters]
    have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
    have callable : TypeAdmissible lexical (.function .word .word) :=
      ⟨binders, .function (.builtin .word) (.builtin .word)⟩
    let innerContext := lexical.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner lexical shape.argument innerContext := by
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
    have innerWord : TypeAdmissible innerContext .word := ⟨binders, .builtin .word⟩
    have instantiation : LocalSchemeInstantiationValid innerContext shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible innerWord) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody innerContext shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local (.tail shape.argumentDistinct head.local_self)
            (.tail shape.argumentDistinct head.local_scheme_requirements_self) instantiation))
        shape.readRaw innerWord (shape.readType ▸ innerWord) ?_
      · rw [shape.readRequirements, shape.readCoercions, shape.readType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .word .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp)
          (.cons shape.argumentScheme argumentExtended (.nil _))
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(x: Word) { return seed; }; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let .lambda [argument] _ _ := expression.form
    | throw (IO.userError "packed factory lambda argument")
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono .word) "packed argument scheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "packed argument requirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "packed argument owner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "packed argument identity"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .word .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "captured factory roots"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "captured factory readFound"
  let ⟨innerReturnFound⟩ ← observed (function.typedBody.lookupStatement? innerReturn.id = some innerReturn) "captured factory innerReturnFound"
  let ⟨expressionFound⟩ ← observed (function.typedBody.lookupExpression? expression.id = some expression) "captured factory expressionFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "captured factory statementFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "captured factory readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "captured factory readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "captured factory readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "captured factory readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "captured factory readCoercions"
  let ⟨innerReturnForm⟩ ← observed (innerReturn.form = .returnStmt (some read.id)) "captured factory innerReturnForm"
  let ⟨innerReturnType⟩ ← observed (innerReturn.type = .word) "captured factory innerReturnType"
  let ⟨lambda⟩ ← observed (expression.form = .lambda [argument] .word [innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .word .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .word .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .word .word) "captured factory statementType"
  return { binder, argument, argumentScheme, argumentRequirements, argumentOwner, argumentDistinct, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }

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
  nodes : function.typedBody.nodes = [.expression sourceShape.read,
    .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement]

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
        if nodes : function.typedBody.nodes = [.expression sourceShape.read,
            .statement sourceShape.innerReturn, .expression sourceShape.expression, .statement sourceShape.statement] then
          return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
            function, signature, functions, signatures, methods, sourceShape, nodes⟩
        else throw (IO.userError "captured factory complete node graph changed")
      else throw (IO.userError "unexpected captured factory methods")
    | _, _ => throw (IO.userError "captured factory declaration count")

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedFixture
/-! Actual compilation, selected inventory and static lambda observations for
one captured Word closure with one Word argument. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
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
  nodes : row.function.typedBody.nodes = [.expression shape.read, .statement shape.innerReturn,
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
abbrev ObservedFactory.readForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readForm
abbrev ObservedFactory.readRaw {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readRaw
abbrev ObservedFactory.readType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readType
abbrev ObservedFactory.readRequirements {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readRequirements
abbrev ObservedFactory.readCoercions {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readCoercions
abbrev ObservedFactory.innerReturnForm {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnForm
abbrev ObservedFactory.innerReturnType {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.innerReturnType
abbrev ObservedFactory.returnStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.returnStatement
abbrev ObservedFactory.bodyRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.read
abbrev ObservedFactory.foundStatement {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.statementFound
abbrev ObservedFactory.foundExpression {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.expressionFound
abbrev ObservedFactory.foundRead {fixture : CompiledFixture} (observed : ObservedFactory fixture) := observed.shape.readFound
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
        let ⟨nodes⟩ ← observeFact (row.function.typedBody.nodes = [.expression shape.read,
          .statement shape.innerReturn, .expression shape.expression, .statement shape.statement]) "packed nodes"
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
    parameters = [observed.argument] ∧ result = .word ∧ body = [observed.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.lambda] at form
        obtain ⟨parametersEq, resultEq, bodyEq⟩ := ExpressionForm.lambda.inj form
        exact ⟨parametersEq.symm, resultEq.symm, bodyEq.symm⟩
      · rcases List.mem_cons.mp rest with impossible | empty
        · cases impossible
        · cases empty

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


end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedSupports
/-! A complete singleton inventory supplies formation and every authentic
captured-read closure body, including the actual nonempty parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal_parameters terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.entryMember
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read
  · rw [actual.source]; exact observed.foundInnerReturn
  · exact observed.innerReturnForm
  · exact observed.innerReturnType

theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal diagnostic expression
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
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function .word .word := by
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
  obtain ⟨support⟩ := actual.support stages terminal diagnostic expression point (registry := registry) (faults := faults)
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
      apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
      have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
      have found := code.sourceFound
      rw [sameSource] at found
      have bodyShape := (observed.lambda_shape found code.sourceForm).2.2
      exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
        receiver
        fixture.source_wellFormed
        (by rw [sameSource]; exact observed.nodes) observed.lambda bodyShape
        (by rw [sameSource]; exact observed.foundInnerReturn) observed.innerReturnForm
        (by rw [sameSource]; exact observed.foundRead) observed.readForm
        observed.readRequirements observed.readCoercions observed.noLocals
        fixture.signature fixture.signature_member (by rw [sameSource]; exact observed.sourceOwner)
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact False.elim (fixture.no_principal support.principal)
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports, family := family, descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedCommon
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted nonzero-parameter factory; retained states refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
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

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedInvocation
/-! Actual one-Word public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

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
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.actual.header.function.context .word (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
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

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
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


end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedPublicExecution
/-! Actual make(10), invoke(99), invoke(123) calls share the original exported
closure and successive returned sessions. Source applications retain both
literal argument vectors and the captured result through the full history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def firstArgument : Core.Word := Core.Word.ofNatModulo 99

def secondArgument : Core.Word := Core.Word.ofNatModulo 123

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ObservedInvocation factory.completion.session factory.handle firstArgument
  firstValue : first.completion.value = .word seed
  second : ObservedInvocation first.completion.session factory.handle secondArgument
  secondValue : second.completion.value = .word seed

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeInvocation factory.completion.session factory.handle firstArgument
  if firstValue : first.completion.value = .word seed then
    let second ← observeInvocation first.completion.session factory.handle secondArgument
    if secondValue : second.completion.value = .word seed then
      return ⟨factory, first, firstValue, second, secondValue⟩
    else throw (IO.userError "second packed call changed its captured seed")
  else throw (IO.userError "first packed call returned its argument instead of its captured seed")

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (entry : Entry) (function : Dynamic.Closure),
      entry.sourceType = .function .word .word ∧ entry.handle = sequence.factory.handle ∧
      entry.source = .closure function ∧ function.parameters = [observed.argument] ∧
      function.resultType = .word ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap

/-- The accepted checker/compiler and original public execution construct all
static supports, closure provenance and the three connected Source applications. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed stages receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ :=
    first_meaning support stages sequence.factory
  obtain ⟨function, source, parameters, result⟩ := factoryTrace.make_closure
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType source parameters handle handleType
    sequence.first sequence.firstValue scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType source parameters handle handleType
    sequence.second sequence.secondValue scope
  exact ⟨support, entry, function, entryType, handle, source, parameters, result,
    initial, first, final, factoryTrace, firstTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed stages sequence receiver
  IO.println "Actual packed closure reuse: arguments 99/123, captured results 10/10, Source applications and returned histories proved"

end Tests.SourceCoreCapturedPacked
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedPackedForward
/-! The actual two packed calls first establish independent Source traces.
Those traces then imply public success at every sufficient execution budget
and every output-validation budget of at least one, on their original starts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedPacked
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

/-- The actual public checkpoint admits all sufficiently large execution
budgets, with one output-validation step already sufficient. Returned states
have the same Source heap as the independently established application. -/
def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle) (argument word : Core.Word)
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
      support.actual.header.function.context .word (.word argument) (.word argument) :=
    .data ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
      ⟨.word argument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word argument⟩
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
      (input := input) started metadata (.singleton (.word argument)) trace atCheckpoint
  refine ⟨publicCheckpoint, accepted, required, ?_⟩
  intro executionFuel outputFuel outcome enough positive resumed
  obtain ⟨publicCompletion, actual, _generation, reached, succeeded, wordValue, _exported,
      indexedAt, _related, history, returnedRegistry⟩ := publicEnough executionFuel outputFuel outcome enough positive resumed
  rw [registryEq] at returnedRegistry
  exact ⟨publicCompletion, succeeded, wordValue,
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      indexedAt.2.2.2, state.atRecipe, returnedRegistry, history⟩, rfl⟩

/-- Both finite observed public calls have an independently justified forward
fuel guarantee on the original checkpoint, with exact captured Word 10 and
Source post-heaps. No Source execution assumption is an input. -/
theorem sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    ∃ support : PublicSupports receiver,
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function .word .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap ∧
        ForwardWordAt support sequence.factory.completion.session [entry] sequence.factory.handle
          firstArgument seed first.heap ∧
        ForwardWordAt support sequence.first.completion.session [entry] sequence.factory.handle
          secondArgument seed final.heap := by
  obtain ⟨support, entry, function, entryType, handle, source, _parameters, _result,
      initial, first, final, factoryTrace, firstTrace, finalTrace⟩ :=
    sequence_meaning fixture observed stages sequence receiver
  exact ⟨support, entry, entryType, handle, initial, first, final, factoryTrace, firstTrace, finalTrace,
    forward_word initial entry (by simp) entryType source handle sequence.first firstTrace,
    forward_word first entry (by simp) entryType source handle sequence.second finalTrace⟩

/-- Use the existing observed sequence once for reflection and preservation. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_forward_meaning fixture observed stages sequence receiver
  IO.println "Actual packed closure reuse: Source reflection and public Word preservation with output fuel 1 proved"

end Tests.SourceCoreCapturedPacked
end
