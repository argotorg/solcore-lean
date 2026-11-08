import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.Staging.Erasure

/-!
# Captured mapping tests

Closures with mapping arguments, named exports and resumption.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingSource
/-! Independent Source typing for the actual captured Word factory with one
mapping argument. The body reads the outer seed after the new argument is installed;
its stable binder identity and original lexical lookup remain explicit. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  argument : TypedBinder
  argumentScheme : argument.scheme = .mono (.mapping .word .word)
  argumentRequirements : argument.schemeRequirements = []
  argumentOwner : argument.id.owner = function.typedBody.owner
  argumentDistinct : argument.id ≠ binder.id
  read : ExpressionNode
  innerReturn : StatementNode
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.function (.mapping .word .word) .word]
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
  expressionRaw : expression.rawType = .function (.mapping .word .word) .word
  expressionType : expression.type = .function (.mapping .word .word) .word
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function (.mapping .word .word) .word

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
    type := .function (.mapping .word .word) .word
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
    have callable : TypeAdmissible lexical (.function (.mapping .word .word) .word) :=
      ⟨binders, .function (.mapping (.builtin .word) (.builtin .word)) (.builtin .word)⟩
    let innerContext := lexical.withLocal shape.argument.id shape.argument.scheme shape.argument.schemeRequirements
    have argumentExtended : BinderExtends function.typedBody.owner lexical shape.argument innerContext := by
      apply BinderExtends.intro
      · exact {
          owned := shape.argumentOwner
          scheme := shape.argumentScheme.symm ▸ SchemeWellFormed.monoAdmissible
            (show TypeAdmissible lexical (.mapping .word .word) from ⟨binders, .mapping (.builtin .word) (.builtin .word)⟩)
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
        (.function (.mapping .word .word) .word) := by
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
    "function make(seed: Word) returns (function(mapping(Word => Word)) returns (Word)) { return lam(x: mapping(Word => Word)) { return seed; }; }"}] }

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
  let ⟨argumentScheme⟩ ← observed (argument.scheme = .mono (.mapping .word .word)) "packed argument scheme"
  let ⟨argumentRequirements⟩ ← observed (argument.schemeRequirements = []) "packed argument requirements"
  let ⟨argumentOwner⟩ ← observed (argument.id.owner = function.typedBody.owner) "packed argument owner"
  let ⟨argumentDistinct⟩ ← observed (argument.id ≠ binder.id) "packed argument identity"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function (.mapping .word .word) .word]) "captured factory returns"
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
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function (.mapping .word .word) .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function (.mapping .word .word) .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function (.mapping .word .word) .word) "captured factory statementType"
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

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingFixture
/-! Actual compilation, selected inventory and static lambda observations for
one captured Word closure with one mapping argument. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
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
  resultType : row.function.inferredBodyType = .function (.mapping .word .word) .word
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
        let ⟨resultType⟩ ← observeFact (row.function.inferredBodyType = .function (.mapping .word .word) .word) "packed factory output type"
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


end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingSupports
/-! A complete singleton inventory supplies formation and every authentic
captured-read closure body, including the actual nonempty parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
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
    (actual : ActualHeader fixture observed.row) : actual.header.function.resultType = .function (.mapping .word .word) .word := by
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

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingCommon
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted nonzero-parameter factory; retained states refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
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
  authority : bootstrap.ExportAuthorityAt
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

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


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
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
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

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
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

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingInvocation
/-! Mapping inputs use the actual metadata encoder and its authentic receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def publicArgument (rows : List (Core.Word × Core.Word)) : SourceCorePublicValues.Value :=
  .mapping .word .word (rows.map (fun row => (.word row.1, .word row.2)))

def sourceArgument (rows : List (Core.Word × Core.Word)) : Dynamic.Value :=
  .mapping .word .word (rows.map (fun row => (.word row.1, .word row.2)))

theorem mapping_input {entries : List Entry} {context : SourceSemantics.Context}
    (rows : List (Core.Word × Core.Word)) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context (.mapping .word .word)
      (publicArgument rows) (sourceArgument rows) := by
  apply RecursiveNamedPublicFunctionHistoryInputs.Input.mapping
  induction rows with
  | nil => exact .empty _ _
  | cons row rest ih =>
    exact .entry (.data ⟨.word row.1, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.1⟩ ⟨.word row.1, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.1⟩)
      (.data ⟨.word row.2, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.2⟩ ⟨.word row.2, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word row.2⟩) ih

structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle (publicArgument argument) runOptions (.ok (.succeeded completion))

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ObservedInvocation session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (publicArgument argument) runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "mapping captured call failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "mapping captured call exhausted")
  | .ok (.succeeded completion) => return ⟨completion, result ▸ executed.property⟩

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (argument : List (Core.Word × Core.Word)) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.actual.header.function.context before source [sourceArgument argument] outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.mapping .word .word) .word)
    {argument : List (Core.Word × Core.Word)} (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source argument (.value (.word word)) after.heap := by
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
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.atRecipe state.registry state.atSession
      (by simpa only [entryHandle] using call.executed) invocation
  have handleType : entry.handle.sourceType = .function (.mapping .word .word) .word := entryHandle ▸ handleType
  have requested := started.requested_exact handleType
  have signature := started.selected.signature handleType
  have projected := started.resultProjection
  rw [signature.2] at projected
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  have sourcesEq : sources = [sourceArgument argument] := by
    cases packing
    rfl
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
  exact ⟨next, sourceSize, by simpa only [sourcesEq, outcomeValue] using trace⟩

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed)
    (first : ObservedPublicRun fixture observed) :
    ∃ entry : Entry,
      entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function (.mapping .word .word) .word ∧
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
  rw [resultType, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.actual.result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.input.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩


end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingPublicExecution
/-! Actual make(10) and two mapping-input calls share the exported closure
and successive public sessions. Each Source application retains the literal
ordered rows, current heap and authentic table at its own input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def firstArgument : List (Core.Word × Core.Word) :=
  [(Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 99),
   (Core.Word.ofNatModulo 1, Core.Word.ofNatModulo 123)]

def secondArgument : List (Core.Word × Core.Word) :=
  [(Core.Word.ofNatModulo 2, Core.Word.ofNatModulo 456)]

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
      entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
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
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry
    (receiver.issued)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ :=
    first_meaning support stages sequence.factory
  obtain ⟨function, source, parameters, result⟩ := factoryTrace.make_closure
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType handle handleType
    sequence.first sequence.firstValue scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType handle handleType
    sequence.second sequence.secondValue scope
  exact ⟨support, entry, function, entryType, handle, source, parameters, result,
    initial, first, final, factoryTrace, firstTrace, finalTrace⟩

/-- The final consumer derives its initial receiver from the accepted compiler
and needs only observations of the three actual public calls. -/
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
  IO.println "Actual mapping closure reuse: duplicate ordered rows, captured results 10/10, Source applications and authentic receivers proved"

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingExportError
/-! A native mapping-input call completes but export fuel is zero. The next
call uses the exact session returned by exportError and the earlier closure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def zeroOutputOptions : SourceCoreExecution.RunOptions :=
  { runOptions with outputValidationFuel := 0 }

structure ObservedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  error : SourceCoreIndexedSession.Error
  returned : SourceCoreExecution.Session artifact
  executed : session.InvokeAt handle (publicArgument argument) zeroOutputOptions
    (.ok (.exportError error returned))

def observeExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ObservedExportError session handle argument) := do
  let executed ← session.invokePackedWithReceipt handle (publicArgument argument) zeroOutputOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "mapping call failed before export")
  | .ok (.outOfFuel _) => throw (IO.userError "mapping execution fuel exhausted")
  | .ok (.succeeded _) => throw (IO.userError "zero output fuel unexpectedly exported a value")
  | .ok (.exportError error returned) => return ⟨error, returned, result ▸ executed.property⟩

/-- The exported session carries the completed Source heap even though no new
public value was produced. The existing handle remains in the same history. -/
theorem export_error_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : List (Core.Word × Core.Word)} (call : ObservedExportError publicSession handle argument)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ∃ source : Dynamic.Value, ∃ after : RetainedState support call.returned entries,
      SourceInvocation support invocation state.heap entry.source argument (.value source) after.heap ∧
      call.returned.ExportsReady := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source,
      after, finalMap, finalWorld, reached, contextAt, issued, extended, _diagnostics,
      _started, _parameterView, _resultView, _exported, actualAt, packing, trace, _result,
      _related, retained, returnedRegistry, returnedReady⟩ :=
    RecursiveNamedPublicActualRegistryExportErrors.public_invoke_export_error
      (completion := state.receiving) state.issued (actualStagePrepared fixture) observed.profile
      support.observations semantic support.family
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.atRecipe state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      state.atSession (by simpa only [entryHandle] using call.executed) invocation
  have sourcesEq : sources = [sourceArgument argument] := by cases packing; rfl
  let next : RetainedState support call.returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := retained }
  exact ⟨source, next, ⟨sourceSize, by simpa only [sourcesEq] using trace⟩,
    actualAt.exportsReady_iff.mpr returnedReady⟩

structure ObservedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  noOutput : ObservedExportError factory.completion.session factory.handle firstArgument
  continued : ObservedInvocation noOutput.returned factory.handle secondArgument
  finalValue : continued.completion.value = .word seed

def observeExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedExportSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let noOutput ← observeExportError factory.completion.session factory.handle firstArgument
  let continued ← observeInvocation noOutput.returned factory.handle secondArgument
  if finalValue : continued.completion.value = .word seed then
    return ⟨factory, noOutput, continued, finalValue⟩
  else throw (IO.userError "export error lost the original captured seed")

/-- The actual compiler and bootstrap supply all static and initial-state
facts. The failed export and following successful call share the same Source
heap and authenticated closure; no native completion is assumed separately. -/
theorem closed_export_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedExportSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ (entry : Entry) (source : Dynamic.Value),
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ noOutput : RetainedState support sequence.noOutput.returned [entry],
      ∃ final : RetainedState support sequence.continued.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value source) noOutput.heap ∧
        sequence.noOutput.returned.ExportsReady ∧
        SourceInvocation support scope noOutput.heap entry.source secondArgument (.value (.word seed)) final.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ := first_meaning support stages sequence.factory
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.factory.ready).exportsReady sequence.factory.authority
  have factoryReady := sequence.factory.executed.exportsReady ready
  obtain ⟨source, noOutput, firstTrace, returnedReady⟩ :=
    export_error_meaning initial entry (by simp) entryType handle sequence.noOutput factoryReady scope
  obtain ⟨final, finalTrace⟩ := invoke noOutput entry (by simp) entryType handle handleType
    sequence.continued sequence.finalValue scope
  exact ⟨receiver, support, entry, source, entryType, handle, initial, noOutput, final,
    factoryTrace, firstTrace, returnedReady, finalTrace⟩

def runExportError : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeExportSequence fixture observed
  have _meaning := closed_export_sequence_meaning fixture observed stages sequence
  IO.println "Actual exportError continuation: output fuel 0, retained mapping-call effects, earlier closure returns 10"

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingForward
/-! The same two observed mapping calls establish independent Source traces.
Those traces imply actual public export on their original starts at every
sufficient execution and output-validation budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
    publicSession.startHandlePacked handle (publicArgument argument) runOptions.inputValidationFuel = .ok checkpoint ∧
    ∃ requiredExecution requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ completion : SourceCoreExecution.Completion publicArtifact,
          outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
          ∃ returned : RetainedState support completion.session entries, returned.heap = after

private theorem forward_word {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    (entryType : entry.sourceType = .function (.mapping .word .word) .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function (.mapping .word .word) .word)
    {argument : List (Core.Word × Core.Word)} {word : Core.Word}
    (call : ObservedInvocation publicSession handle argument)
    (exportsReady : publicSession.ExportsReady)
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
      (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      support.supports fixture.source_wellFormed state.history entry member entryType
      (mapping_input argument) state.registry (state.atSession.exportsReady_iff.mp exportsReady)
      started (.singleton (sourceArgument argument)) trace atCheckpoint
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

/-- Actual bootstrap authority and successful public transitions supply export
readiness. No Source execution or output-success assumption is supplied. -/
theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
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
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ := first_meaning support stages sequence.factory
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType handle handleType
    sequence.first sequence.firstValue scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType handle handleType
    sequence.second sequence.secondValue scope
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.factory.ready).exportsReady sequence.factory.authority
  have factoryReady := sequence.factory.executed.exportsReady ready
  have firstReady := sequence.first.executed.exportsReady factoryReady
  exact ⟨receiver, support, entry, entryType, handle, initial, first, final, factoryTrace, firstTrace, finalTrace,
    forward_word initial entry (by simp) entryType handle handleType sequence.first factoryReady firstTrace,
    forward_word first entry (by simp) entryType handle handleType sequence.second firstReady finalTrace⟩

/-- Run the same three-call scenario once and check both proof directions. -/
def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed stages sequence
  IO.println "Actual mapping closure reuse: Source reflection and public export at sufficient fuel, with exact receivers and histories proved"

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingInitialForward
/-! The same actual factory and mapping calls close initial general-output
preservation. The independent factory trace determines both fuel bounds at
its original checkpoint, before any successful resume is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.sourceType = .function (.mapping .word .word) .word ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

private theorem forward_initial {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed)
    {invocation : Staging.Recursive.Scope} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : SourceCall support support.actual.header invocation ⟨[]⟩ [.word seed] (.value sourceResult) after) :
    InitialForwardAt support first after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
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
  rw [rawResult, support.actual.result_type] at requested
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
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
  exact ⟨completion, succeeded, actualAt.2.1.trans (exported.source_type requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩

/-- Checker, compiler, static support and observed public calls supply the
independent factory trace used by the generalized initial output theorem. -/
theorem closed_sequence_initial_forward_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (sourceResult : Dynamic.Value) (after : Dynamic.Heap),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word seed] (.value sourceResult) after ∧
      InitialForwardAt support sequence.factory after := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨entry, _type, _handle, _handleType, initial, factoryTrace⟩ := first_meaning support stages sequence.factory
  exact ⟨receiver, support, entry.source, initial.heap, factoryTrace,
    forward_initial support sequence.factory factoryTrace⟩

/-- One real three-call sequence exercises reflection, repeated direct export
and initial named export without rerunning the program for proof premises. -/
def runInitialForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _direct := closed_sequence_forward_meaning fixture observed stages sequence
  have _initial := closed_sequence_initial_forward_meaning fixture observed stages sequence
  IO.println "Actual mapping closure reuse: initial named and repeated direct public export, Source results 10/10 and exact session histories proved"

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingNamedExportErrors
/-! Initial and following named export errors preserve the actual completed
Source heap. A closure exported between those errors remains callable. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMapping
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedNamedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key [.word seed] zeroOutputOptions.inputValidationFuel = .ok checkpoint
  error : SourceCoreIndexedSession.Error
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt key [.word seed] zeroOutputOptions (.ok (.exportError error returned))

def observeNamedExportError {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamedExportError session key) := do
  match started : session.start key [.word seed] zeroOutputOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key [.word seed] zeroOutputOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "named factory failed before export")
    | .ok (.outOfFuel _) => throw (IO.userError "named factory execution exhausted")
    | .ok (.succeeded _) => throw (IO.userError "zero output fuel exported a function")
    | .ok (.exportError error returned) =>
      return ⟨checkpoint, started, error, returned, result ▸ executed.property⟩

structure ObservedInitialNamedExport (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : ObservedNamedExportError session observed.row.key

def observeInitialNamedExport (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedInitialNamedExport fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let bootstrap ← opened.val.bootstrapWithExportReceipt
  match ready : bootstrap.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "initial named export bootstrap exhausted")
  | .ready session =>
    let call ← observeNamedExportError session observed.row.key
    return ⟨opened.val, opened.property, bootstrap.val, bootstrap.property.1,
      bootstrap.property.2, session, ready, call⟩

private theorem same_recipe {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem initial_named_export_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed) (first : ObservedInitialNamedExport fixture observed) :
    ∃ source : Dynamic.Value, ∃ state : RetainedState support first.call.returned [],
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word seed] (.value source) state.heap ∧ first.call.returned.ExportsReady := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted first.opened first.call.started
  have same := same_recipe opened.compiled_recipe fixture.issued
  cases same
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.actual.header := by
    have member := selected.member
    change List.Mem _ _ at member
    rw [support.header_list] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.actual.header.function.context
      (support.actual.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.actual.input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.actual.header support.input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.packet.header.named.specialized support.input.prepared.available)) := by
    rw [support.headerEq]
    exact support.packet.sourceAt
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, caller, actual, generation,
      value, finalStore, capture, sourceSize, source, after, finalMap, finalWorld,
      exported, returnedAt, trace, _result, reached, _related, retained, registry, ready⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedExportErrors.public_run_export_error_seeds
      (inputs := [support.input]) (rows := support.rows) (distinct := by simp)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened) (fresh := first.fresh)
      (ready := .single first.ready) (authority := first.authority) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
      first.call.started first.call.executed support.descriptor
  let state : RetainedState support first.call.returned [] := {
    artifact := artifact, session := actual, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := started.recipe_eq, receiving := receiving, issued := issued,
    extension := extended, registry := (congrArg (·.registry) contextAt).symm ▸ registry,
    history := retained }
  exact ⟨source, state, ⟨support.input.prepared.available, _, sourceSize, sourceAt, trace⟩,
    returnedAt.exportsReady_iff.mpr ready⟩

theorem next_named_export_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamedExportError publicSession observed.row.key)
    (exportsReady : publicSession.ExportsReady) (invocation : Staging.Recursive.Scope) :
    ∃ source : Dynamic.Value, ∃ after : RetainedState support call.returned entries,
      SourceCall support support.actual.header invocation state.heap [.word seed] (.value source) after.heap ∧
      call.returned.ExportsReady := by
  have selected : ∀ request : RecursiveNamedPublicHistoryFrontdoor.Started
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows) fixture.recipePrepared
      call.checkpoint state.session observed.row.key [.word seed] zeroOutputOptions.inputValidationFuel
      state.world state.store, request.header = support.actual.header := by
    intro request
    have only : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows →
        header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact only _ request.selected.member
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨request, arguments, inputs, receiving, contextAt, issued, extended, _diagnostics,
      actual, generation, value, finalStore, capture, sourceSize, source, after, finalMap, finalWorld,
      exported, returnedAt, trace, _result, reached, _related, retained, registry, ready⟩ :=
    RecursiveNamedPublicActualRegistryNamedExportErrors.public_run_export_error_retains
      (inputs := [support.input]) (rows := support.rows) (stagePrepared := actualStagePrepared fixture)
      (completion := state.receiving) (receiver := state.issued) (profile := observed.profile)
      (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (complete := support.complete) (history := state.history)
      (atRegistry := state.registry) (atRecipe := state.atRecipe) (atSession := state.atSession)
      (exportsReady := exportsReady) (invocation := invocation)
      (inputsFor := by
        intro request
        refine ⟨[.word seed], ?_⟩
        rw [selected request, support.actual.input_types]
        exact .cons (.data
          ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
          ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil)
      (descriptors := by intro request; rw [selected request]; exact ⟨support.descriptor⟩)
      call.started call.executed
  have args : arguments = [.word seed] := by
    rw [selected request, support.actual.input_types] at inputs
    cases inputs with
    | cons head tail =>
      cases tail
      generalize rawEq : TypeSystem.Ty.word = raw at head
      generalize publicEq : SourceCorePublicValues.Value.word seed = publicValue at head
      cases head with
      | retained entry member => cases publicEq
      | data typed meaning =>
        subst publicValue
        obtain ⟨data, publicEq, meaning⟩ := meaning
        cases data <;> simp_all [SourceCoreIndexedSession.DataInput.publicValue]
        cases meaning
        rfl
      | product => cases publicEq
      | constructed => cases publicEq
      | mapping => cases publicEq
      | comptime => cases rawEq
  let next : RetainedState support call.returned entries := {
    artifact := state.artifact, session := actual, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := reached, atSession := returnedAt,
    atRecipe := state.atRecipe, receiving := receiving, issued := issued,
    extension := state.extension.trans extended,
    registry := (congrArg (·.registry) contextAt).symm ▸ registry, history := retained }
  exact ⟨source, next, ⟨request.rawD, request.function, sourceSize, selected request ▸ request.sourceAt,
    by simpa only [args] using trace⟩, returnedAt.exportsReady_iff.mpr ready⟩

structure ObservedNamedFactoryCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamedFactoryCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamedFactoryCall session key) := do
  match started : session.start key [.word seed] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key [.word seed] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "following factory failed")
    | .ok (.outOfFuel _) => throw (IO.userError "following factory execution exhausted")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.succeeded completion) =>
      match returned : completion.value with
      | .function handle => return ⟨checkpoint, started, completion, result ▸ executed.property, handle, returned⟩
      | _ => throw (IO.userError "following factory did not return a function")

theorem named_factory_meaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamedFactoryCall publicSession observed.row.key) (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function (.mapping .word .word) .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.actual.header invocation state.heap [.word seed] (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.input] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.actual.header := by
    have only : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows →
        header = support.actual.header := by
      intro header member
      rw [support.header_list] at member
      exact List.mem_singleton.mp member
    exact only _ request.selected.member
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [selected, support.actual.input_types]
    exact .cons (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have registryAt : request.encodedValues.registry = state.receiving.result.context.registry := by
    apply request.started.simple_registry state.registry
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.descriptor
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, nativeValue, finalStore, capture, sourceSize, outcome, heap, mapping, world,
      succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _result,
      caller, source, payload, sourceValue, _nativePayload, _related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.input]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving) (receiver := state.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member))
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := fixture.recipePrepared) (selected := request.selected) (caller := state.caller)
      (history := state.history) (atCheckpoint := request.atCheckpoint) (started := request.started)
      (invocation := invocation) (inputReceipts := inputs)
      (metadata := by rw [registryAt]; exact .refl _) (sourceAt := request.sourceAt)
      call.started call.executed call.returned descriptor
  let entry : Entry := ⟨request.header.function.resultType, source, call.handle, payload,
    request.header.output, runOptions.outputValidationFuel⟩
  let after : RetainedState support call.completion.session (entries ++ [entry]) := {
    artifact := state.artifact, session := actual.session, mapping := mapping, world := world,
    heap := heap, store := finalStore, caller := caller, atSession := returnedAt, atRecipe := state.atRecipe,
    receiving := state.receiving, issued := state.issued, extension := state.extension,
    registry := registryAt ▸ request.started.returned_registry succeeded, history := continued }
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selected, support.actual.result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, selected ▸ request.sourceAt, ?_⟩
  · change request.header.function.resultType = .function (.mapping .word .word) .word
    rw [selected, support.actual.result_type]
  · simpa only [entry, after, sourceValue] using trace

structure ObservedNamedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  first : ObservedInitialNamedExport fixture observed
  factory : ObservedNamedFactoryCall first.call.returned observed.row.key
  noOutput : ObservedNamedExportError factory.completion.session observed.row.key
  reused : ObservedInvocation noOutput.returned factory.handle firstArgument
  result : reused.completion.value = .word seed

def observeNamedExportSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedNamedExportSequence fixture observed) := do
  let first ← observeInitialNamedExport fixture observed
  let factory ← observeNamedFactoryCall first.call.returned observed.row.key
  let noOutput ← observeNamedExportError factory.completion.session observed.row.key
  let reused ← observeInvocation noOutput.returned factory.handle firstArgument
  if result : reused.completion.value = .word seed then
    return ⟨first, factory, noOutput, reused, result⟩
  else throw (IO.userError "named export error lost earlier closure capture")

/-- All four observations are consumed by one connected Source execution
sequence. The heap after each actual export error is the next call's heap. -/
theorem closed_named_export_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedNamedExportSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ (firstSource followingSource : Dynamic.Value) (entry : Entry),
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ first : RetainedState support sequence.first.call.returned [],
      ∃ factory : RetainedState support sequence.factory.completion.session [entry],
      ∃ noOutput : RetainedState support sequence.noOutput.returned [entry],
      ∃ reused : RetainedState support sequence.reused.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value firstSource) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word seed] (.value entry.source) factory.heap ∧
        SourceCall support support.actual.header scope factory.heap [.word seed] (.value followingSource) noOutput.heap ∧
        sequence.first.call.returned.ExportsReady ∧ sequence.noOutput.returned.ExportsReady ∧
        SourceInvocation support scope noOutput.heap entry.source firstArgument (.value (.word seed)) reused.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨firstSource, first, firstTrace, firstReady⟩ := initial_named_export_meaning support stages sequence.first
  obtain ⟨entry, entryType, handle, handleType, factory, factoryTrace⟩ := named_factory_meaning first sequence.factory scope
  have factoryReady := sequence.factory.executed.exportsReady firstReady
  obtain ⟨followingSource, noOutput, nextTrace, noOutputReady⟩ :=
    next_named_export_meaning factory sequence.noOutput factoryReady scope
  obtain ⟨reused, reusedTrace⟩ := invoke noOutput entry (by simp) entryType handle handleType
    sequence.reused sequence.result scope
  exact ⟨receiver, support, firstSource, followingSource, entry, entryType, handle,
    first, factory, noOutput, reused, firstTrace, factoryTrace, nextTrace, firstReady, noOutputReady, reusedTrace⟩

def runNamedExportErrors : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeNamedExportSequence fixture observed
  have _meaning := closed_named_export_sequence_meaning fixture observed stages sequence
  IO.println "Actual named export errors: initial export error, exported closure, following export error, retained closure returns 10"

end Tests.SourceCoreCapturedMapping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingResumptionRuntime
/-! Each direct call resumes the returned checkpoint twice with positive fuel
before finishing. The original checkpoint is never executed a second time. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMappingResumption
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedMapping

structure ResumedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.startHandlePacked handle (publicArgument argument)
    runOptions.inputValidationFuel = .ok checkpoint
  first : SourceCoreExecution.Checkpoint artifact
  firstExhausted : checkpoint.ResumeAt 1 0 (.outOfFuel first)
  second : SourceCoreExecution.Checkpoint artifact
  secondExhausted : first.ResumeAt 1 0 (.outOfFuel second)
  completion : SourceCoreExecution.Completion artifact
  finished : second.ResumeAt (runOptions.executionFuel - 2) runOptions.outputValidationFuel
    (.succeeded completion)

theorem ResumedInvocation.chain {artifact : SourceCoreExecution.Artifact}
    {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}
    {argument : List (Core.Word × Core.Word)} (call : ResumedInvocation session handle argument) :
    call.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded call.completion) := by
  have chain := SourceCoreExecution.Checkpoint.ResumeChain.more call.firstExhausted
    (.more call.secondExhausted (.single call.finished))
  simpa only [runOptions] using chain

def ResumedInvocation.observed {artifact : SourceCoreExecution.Artifact}
    {session : SourceCoreExecution.Session artifact} {handle : SourceCorePublicValues.Handle}
    {argument : List (Core.Word × Core.Word)} (call : ResumedInvocation session handle argument) :
    ObservedInvocation session handle argument :=
  ⟨call.completion, call.checkpoint, call.started, call.chain.collapse⟩

def observeResumedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : List (Core.Word × Core.Word)) : IO (ResumedInvocation session handle argument) := do
  match started : session.startHandlePacked handle (publicArgument argument)
      runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let first ← checkpoint.resumeWithReceipt 1 0
    match firstResult : first.val with
    | .outOfFuel firstCheckpoint =>
      let second ← firstCheckpoint.resumeWithReceipt 1 0
      match secondResult : second.val with
      | .outOfFuel secondCheckpoint =>
        let final ← secondCheckpoint.resumeWithReceipt (runOptions.executionFuel - 2)
          runOptions.outputValidationFuel
        match finalResult : final.val with
        | .succeeded completion =>
          return ⟨checkpoint, started, firstCheckpoint, firstResult ▸ first.property,
            secondCheckpoint, secondResult ▸ second.property,
            completion, finalResult ▸ final.property⟩
        | .failed _ _ => throw (IO.userError "resumed captured call failed")
        | .exportError error _ => throw (IO.userError (reprStr error))
        | .outOfFuel _ => throw (IO.userError "final captured-call resume exhausted")
      | _ => throw (IO.userError "second positive-fuel resume did not exhaust")
    | _ => throw (IO.userError "first positive-fuel resume did not exhaust")

structure ResumedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ResumedInvocation factory.completion.session factory.handle firstArgument
  firstValue : first.completion.value = .word seed
  second : ResumedInvocation first.completion.session factory.handle secondArgument
  secondValue : second.completion.value = .word seed

def ResumedSequence.observed {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (sequence : ResumedSequence fixture observed) : ObservedSequence fixture observed :=
  ⟨sequence.factory, sequence.first.observed, sequence.firstValue,
    sequence.second.observed, sequence.secondValue⟩

def observeResumedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ResumedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeResumedInvocation factory.completion.session factory.handle firstArgument
  if firstValue : first.completion.value = .word seed then
    let second ← observeResumedInvocation first.completion.session factory.handle secondArgument
    if secondValue : second.completion.value = .word seed then
      return ⟨factory, first, firstValue, second, secondValue⟩
    else throw (IO.userError "second resumed call changed captured seed")
  else throw (IO.userError "first resumed call changed captured seed")

end Tests.SourceCoreCapturedMappingResumption
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedMappingResumptionPublicExecution
/-! Finite public resumptions retain the same independent Source execution,
current captured heap, authentic receiver, and reusable function history.
The forward guarantee concerns total execution fuel and the final output budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMappingResumption
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedMapping
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardChainWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (entries : List Entry) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeChain executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

/-- Collapse changes neither the actual terminal outcome nor the export event.
Intermediate output budgets are irrelevant because those events exhausted execution fuel. -/
theorem forward_chain {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {checkpoint : SourceCoreExecution.Checkpoint artifact} {entries : List Entry}
    {handle : SourceCorePublicValues.Handle} {argument : List (Core.Word × Core.Word)}
    {word : Core.Word} {after : Dynamic.Heap}
    (started : session.startHandlePacked handle (publicArgument argument)
      runOptions.inputValidationFuel = .ok checkpoint)
    (forward : ForwardWordAt support session entries handle argument word after) :
    ForwardChainWordAt support checkpoint entries word after := by
  obtain ⟨original, accepted, requiredExecution, requiredOutput, enough⟩ := forward
  have same : original = checkpoint := Except.ok.inj (accepted.symm.trans started)
  subst original
  exact ⟨requiredExecution, requiredOutput, fun executionFuel outputFuel outcome
    enoughExecution enoughOutput chain =>
      enough executionFuel outputFuel outcome enoughExecution enoughOutput chain.collapse⟩

/-- All Source traces and retained states come from the actual checker/compiler,
bootstrap, and two resumed calls. No Source execution or export-success law is assumed. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ResumedSequence fixture observed) :
    sequence.first.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded sequence.first.completion) ∧
    sequence.second.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded sequence.second.completion) ∧
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap ∧
        ForwardChainWordAt support sequence.first.checkpoint [entry] seed first.heap ∧
        ForwardChainWordAt support sequence.second.checkpoint [entry] seed final.heap := by
  obtain ⟨receiver, support, entry, entryType, handle, initial, first, final,
    factoryTrace, firstTrace, secondTrace, firstForward, secondForward⟩ :=
    closed_sequence_forward_meaning fixture observed stages sequence.observed
  exact ⟨sequence.first.chain, sequence.second.chain,
    receiver, support, entry, entryType, handle, initial, first, final,
    factoryTrace, firstTrace, secondTrace,
    forward_chain sequence.first.started firstForward,
    forward_chain sequence.second.started secondForward⟩

/-- One factory and two direct calls; each direct call has two genuine positive
fuel exhaustion events before its final completion. -/
def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeResumedSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual mapping closure resumptions: two positive exhaustion events per call, captured 10/10, Source and sufficient-total-fuel histories proved"

end Tests.SourceCoreCapturedMappingResumption
end
