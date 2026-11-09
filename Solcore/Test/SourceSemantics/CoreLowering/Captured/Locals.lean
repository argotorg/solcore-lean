import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.MethodPrincipal
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.InitializedPublicBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectHistories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedCanonicalSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry

/-!
# Captured local tests

Closures that capture locals, reuse of captures, and direct sequences.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalSource
/-! Independent Source typing for a factory that initializes a fresh lexical
local from its parameter and returns a closure capturing that local cell. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreCapturedLocal
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
  roots : function.typedBody.roots = [.statement initialized.id, .statement statement.id]
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
  lambda : expression.form = .lambda [] .word [innerReturn.id]
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
  have same : statements = [shape.initialized.id, shape.statement.id] :=
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
  refine ⟨BodyFacts.cons letFacts (BodyFacts.singleton facts), rfl, ?_⟩
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
    have callable : TypeAdmissible innerContext (.function .unit .word) :=
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
    have expressionTyped : ExpressionHasType function.typedBody innerContext shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp)
          (.nil _)
          (.singleton (.returnValue (lookupStatement?_sound shape.innerReturnFound)
            shape.innerReturnForm readTyped shape.innerReturnType))
          (by exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩)) shape.expressionRaw
        callable (shape.expressionType ▸ callable) ?_
      rw [shape.requirements, shape.coercions, shape.expressionType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have initializedTyped : StatementHasType function.typedBody
        ⟨.function .unit .word, 0⟩ lexical shape.initialized.id innerContext letFacts := by
      apply StatementHasType.letInitialized (lookupStatement?_sound shape.initializedFound) shape.initializedForm
      · simpa only [shape.localScheme, TypeSystem.Scheme.mono] using initialReadTyped
      · rw [shape.localScheme]; rfl
      · rw [shape.localScheme]; rfl
      · exact localExtended
      · exact shape.initializedType
    exact ⟨_, .cons initializedTyped (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.returnStatement expressionTyped shape.statementType))⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make(seed: Word) returns (function() returns (Word)) { let local: Word = seed; return lam() { return local; }; }"}] }

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
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono .word) "packed argument scheme"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "packed argument requirements"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "captured local ordinary binder"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "packed argument owner"
  let ⟨localDistinct⟩ ← observed (localBinder.id ≠ binder.id) "packed argument identity"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "captured factory inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "captured factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement statement.id]) "captured factory roots"
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
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "captured factory lambda"
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

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalFixture
/-! Actual compilation, selected inventory and static lambda observations for
a closure capturing an initialized lexical local. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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
    parameters = [] ∧ result = .word ∧ body = [observed.innerReturn.id] := by
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


end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalBodyReceipt
/-! The named body receipt comes from the actual accepted full two-statement
lowering, including local initialization. It is not a terminal-only receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.statements {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    actual.header.function.body = [observed.shape.initialized.id, observed.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.roots] at accepted
  exact (Except.ok.inj accepted).symm

/-- The complete original body has the supported initialized-let/return shape. -/
theorem ActualHeader.lexical_shape {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    CallableIndexedOwnedPreparedStagedLexicalTree.Shape actual.header.function.source actual.header.function.body := by
  rw [actual.source, actual.statements]
  exact .initialized observed.shape.initializedFound observed.shape.initializedForm
    (.returnValue [] observed.foundStatement observed.returnStatement)

theorem ActualHeader.lexical_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :=
  CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted
    actual.aligned.accepted actual.lexical_shape actual.aligned.projection

/-- The lexical bundle keeps the same actual Header provenance and compiler receipt. -/
def ActualHeader.lexical_body {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.row
  prepared := actual.prepared
  instantiation := CallableNamedMetadata.instantiation observed.row
  aligned := actual.aligned
  layouts := actual.aligned.layouts
  compilation := .lexical receipt }

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

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace: the
lambda copies the local's cell, and the copy holds the local's value. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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
    {value : Dynamic.Value} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda [] .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ (function : Dynamic.Closure) (captured : Dynamic.Environment),
      value = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      function.captured = captured ∧ function.context = context ∧
      Dynamic.EnvironmentCopies source environment before captured after := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, snapshot⟩
  | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem initialized_read
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {word : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (uncoerced : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location { type := .word, value := some (.word word) })
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    value = .word word ∧ after = before := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw with
    | «local» _ actualLookup actualRead _ initialized =>
      have sameLocation := actualLookup.functional lookup
      subst_vars
      have sameCell := actualRead.functional read
      cases sameCell
      exact ⟨Option.some.inj initialized.symm, rfl⟩
    | localEmptyMapping _ actualLookup actualRead _ _ empty _ =>
      have sameLocation := actualLookup.functional lookup
      subst_vars
      have sameCell := actualRead.functional read
      cases sameCell
      cases empty
  | generalizedLocal contains otherForm _ actualLookup actualRead descriptor _ _ _ =>
    have nodeEq := same contains
    cases nodeEq
    rw [form] at otherForm
    cases otherForm
    have sameLocation := actualLookup.functional lookup
    subst_vars
    have sameCell := actualRead.functional read
    cases sameCell
    cases descriptor

/-- Any successful actual factory Source call returns the very closure created
by its terminal lambda after the local cell allocation. -/
theorem ActualHeader.returned_capture
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word} {source : Dynamic.Value}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry
        (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
          fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected))
      size invocation context before (.global global) [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      BinderExtends actual.header.function.source.owner actual.header.context observed.localBinder function.context ∧
      ∃ location, Dynamic.Environment.LooksUp function.captured observed.localBinder.id location ∧
        Dynamic.Heap.Reads after location { type := .word, value := some (.word word) } := by
  have parameters : actual.header.function.parameters = [observed.shape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  have bodyEq : actual.header.function.body = [observed.shape.initialized.id, observed.statement.id] := by
    apply statement_roots_injective
    rw [← actual.header.agreement.roots, actual.source, observed.roots]
    rfl
  have initializedFound : child.source.lookupStatement? observed.shape.initialized.id =
      some observed.shape.initialized := by
    rw [sourceEq, actual.source]
    exact observed.shape.initializedFound
  have statementFound : child.source.lookupStatement? observed.statement.id = some observed.statement := by
    rw [sourceEq, actual.source]
    exact observed.foundStatement
  have expressionFound : child.source.lookupExpression? observed.expression.id = some observed.expression := by
    rw [sourceEq, actual.source]
    exact observed.foundExpression
  have resultType : actual.header.function.resultType = .function .unit .word := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact observed.resultType
  rw [resultType] at converted
  cases converted
  rw [parameters] at parametersAllocated
  cases parametersAllocated with
  | cons parameterAllocation remaining =>
    cases remaining
    have parameterCell := parameterAllocation.reads_new
    simp only [observed.binderScheme, TypeSystem.Scheme.mono] at parameterCell
    rw [bodyEq] at body
    have same {other : StatementNode}
        (contains : ContainsStatement child.source observed.shape.initialized.id other) :
        other = observed.shape.initialized :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans initializedFound)
    cases body with
    | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
    | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
    | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
    | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
    | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | returnUnit contains otherForm =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | returnValue contains otherForm _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | discard contains otherForm _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | letUninitialized contains otherForm _ _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | assignBare contains otherForm _ _ _ _
    | assignProjected contains otherForm _ _ _ _ _ _
    | bitNotProjected contains otherForm _ _ _ _ _
    | bitNotBare contains otherForm _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | letGeneralized contains form _snapshot _captures polymorphic _extended _allocated _next =>
      have nodeEq := same contains
      cases nodeEq
      rw [observed.shape.initializedForm] at form
      cases form
      exact False.elim (polymorphic (by simp [observed.localScheme, TypeSystem.Scheme.mono]))
    | letInitialized contains form initializer _mono extended allocated next =>
      rename_i localLocation
      have nodeEq := same contains
      cases nodeEq
      rw [observed.shape.initializedForm] at form
      cases form
      obtain ⟨sameValue, sameHeap⟩ := initialized_read unique
        (by rw [sourceEq, actual.source]; exact observed.shape.initialReadFound)
        observed.shape.initialReadForm observed.shape.initialReadCoercions
        .head parameterCell initializer.sound.value_plain
      subst_vars
      obtain ⟨function, captured, valueEq, params, result, captures, contextEq, copy⟩ :=
        lambda_shape unique expressionFound observed.lambda observed.coercions
          (returned_expression unique statementFound observed.returnStatement next)
      obtain ⟨location, lookup⟩ : ∃ location,
          Dynamic.Environment.LooksUp captured observed.localBinder.id location := by
        cases copy with
        | shared _ _ => exact ⟨_, .head⟩
        | copied _ _ _ _ => exact ⟨_, .head⟩
      obtain ⟨original, originalLookup, reads⟩ := copy.looksUp lookup
      have sameOriginal := originalLookup.functional .head
      subst sameOriginal
      refine ⟨function, valueEq, params, result, ?_, location, ?_, ?_⟩
      · rw [contextEq, ← sourceEq]
        exact extended
      · rw [captures]
        exact lookup
      · exact reads _ (by simpa only [observed.localScheme, TypeSystem.Scheme.mono] using allocated.reads_new)

/-- The structural consequence used by generic direct invocation. -/
theorem ActualHeader.returned_closure
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word} {source : Dynamic.Value}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry
        (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
          fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected))
      size invocation context before (.global global) [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  obtain ⟨function, value, parameters, result, _extended, _location, _captured, _cell⟩ :=
    actual.returned_capture sourceAt applied
  exact ⟨function, value, parameters, result⟩

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalMetadata
/-! The actual six-node source supplies original policy metadata for both the
initializer's seed read and the closure body's distinct captured-local read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalClosureFamily
/-! Every authentic returned closure of this compiled program receives the
body-reached single-read certificate. The initializer read elsewhere in the
same source remains distinct and contributes only its own original metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence_on (actualStagePrepared fixture)
      code support provenance receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.metadata support.caller.named)
      bodyShape (by rw [sameSource]; exact observed.foundInnerReturn) observed.innerReturnForm
      (by rw [sameSource]; exact observed.foundRead) observed.readForm
      observed.readRequirements observed.readCoercions observed.noLocals
      fixture.signature fixture.signature_member (by rw [sameSource]; exact observed.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalRuntime
/-! Genuine public bootstrap, factory execution and receiving diagnostics for
this accepted lexical-capture factory; receipts refer to exact sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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


structure ObservedInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) where
  completion : SourceCoreExecution.Completion artifact
  executed : session.InvokeAt handle .unit runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observeInvocation {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedInvocation session handle) := do
  let executed ← session.invokePackedWithReceipt handle .unit runOptions
  match result : executed.val with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (.failed _ _) => throw (IO.userError "local capture public invocation failed")
  | .ok (.exportError error _) => throw (IO.userError (reprStr error))
  | .ok (.outOfFuel _) => throw (IO.userError "local capture public invocation exhausted")
  | .ok (.succeeded completion) =>
    if returned : completion.value = .word seed then
      pure ⟨completion, result ▸ executed.property, returned⟩
    else throw (IO.userError "local capture did not preserve the initialized value 10")

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalSyntax
/-! The actual Source typing provides the lexical extension and both child
judgments for the accepted initializer/return body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ObservedFactory.local_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.localBinder.id = .ok observed.localBinder := by
  have distinct : observed.binder.id ≠ observed.localBinder.id := Ne.symm observed.shape.localDistinct
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialReadForm, observed.shape.initializedForm,
    observed.readForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.localOwner, distinct, observed.shape.localScheme, TypeSystem.Scheme.mono,
    observed.shape.localRequirements]

def childSyntax {fixture : CompiledFixture} (observed : ObservedFactory fixture) (id : ExpressionId) : Prop :=
  id = observed.shape.initialRead.id ∨ id = observed.expression.id

theorem ActualHeader.lexical_syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (childSyntax observed)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  have body := actual.statements
  rw [source] at typed
  rw [observed.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, body]
  have unique : NodeOccurrencesUnique observed.row.function.typedBody := source ▸ actual.header.unique
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
          (Or.inl rfl)
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.foundStatement)
          cases same
          rw [observed.returnStatement] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.foundStatement observed.returnStatement type
            observed.foundExpression
            (observed.shape.expressionType.trans actual.result_type.symm)
            (by simpa only [observed.shape.expressionType, actual.result_type] using expression)
            (Or.inr rfl)
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.foundStatement)
          cases same
          simp_all [observed.returnStatement]
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

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalSupports
/-! The actual singleton inventory packages full lexical named-body coverage
and every retained captured-read closure body for the same public model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

/-- Every child is built at the context and scope reached by the actual
accepted lexical lowering. The two finite syntax cases supply compiler facts,
not an assumed body execution law. -/
theorem ActualHeader.lexical_support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) observed.entryMember receipt stages.registry actual.lexical_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  obtain initial | lambda := approved
  · subst id
    have same : node = observed.shape.initialRead :=
      Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.shape.initialReadFound))
    subst node
    obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
      actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
      (by rw [actual.source]; exact observed.metadata actual.prepared.named)
      (stages.registry.source selected) (stages.registry.evidence selected) fields
      (by rw [stages.registry.source selected]; exact declarations)
      (by rw [stages.registry.source selected]; exact found) observed.shape.initialReadForm
      (by rw [stages.registry.source selected]; exact typed)
      (by rw [stages.registry.source selected]; exact accepted)
    exact .recursive root
  · subst id
    have same : node = observed.expression :=
      Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.foundExpression))
    subst node
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedNamedLexicalLambdaFormation.of_expression
      actual.prepared actual.aligned actual.diagnostic fixture.source_wellFormed observed.profile selected
      found observed.lambda (by rw [actual.source]; exact observed.owned)
      observed.requirements observed.coercions (by simp only [observed.noLocals, List.find?_nil])
      (by rw [actual.source]; exact observed.read)
      (by rw [actual.source]; exact observed.foundInnerReturn) observed.innerReturnForm observed.innerReturnType
      fields declarations typed accepted native
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate actual.header fixture.source_wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.recipe.compiled.sourceProgram)
        actual.header.function.context actual.header.function.source := by
      rw [actual.header.frame.context, actual.header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact .formation formation
      (by rw [stages.registry.source selected]
          exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields actual.header.extended)).transport fields)
      (by rw [stages.registry.evidence selected]
          exact fields.covers (RecursiveNamedInitialContextValidity.covers actual.header.frame actual.header.extended))


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
  let rows : Inventory [input] := .cons packet .nil
  have headerList : headers rows = [actual.header] := by
    simp only [rows, headers, sameHeader]
  obtain ⟨receipt⟩ := actual.lexical_receipt
  let body := actual.lexical_body receipt
  obtain ⟨support⟩ := actual.lexical_support stages receipt (registry := registry) receiver
  let terminals : ∀ header, header ∈ headers rows → Body header := fun header member => by
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    exact same ▸ body
  have supports : ∀ header (member : header ∈ headers rows),
      Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
        (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
    intro header member
    have same : header = actual.header := by simpa only [headerList, List.mem_singleton] using member
    subst header
    simpa only [headerList, terminals, body, ActualHeader.lexical_body,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support, ObservedStages.registry,
      actualStagePrepared] using support
  exact ⟨{
    input := input, packet := packet, actual := actual, headerEq := sameHeader, rows := rows, rowsEq := rfl
    complete := by rw [headerList]; exact actual.complete stages
    terminals := terminals, supports := supports
    family := fun association => actual.closure_family stages receiver association
    descriptor := actual.descriptor stages }⟩

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalCommon
/-! Source calls and retained histories use the same actual returned public
sessions for the factory and subsequent closure invocations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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


theorem SourceCall.make_closure {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.actual.header invocation before [.word word] (.value source) after) :
    ∃ function, source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  exact support.actual.returned_closure sourceAt applied

/-- Allocation and capture are read from the same independent Source trace,
including the initialized cell in the actual factory result heap. -/
theorem SourceCall.make_capture {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.actual.header invocation before [.word word] (.value source) after) :
    ∃ function, source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      BinderExtends support.actual.header.function.source.owner support.actual.header.context
        observed.localBinder function.context ∧
      ∃ location, Dynamic.Environment.LooksUp function.captured observed.localBinder.id location ∧
        Dynamic.Heap.Reads after location { type := .word, value := some (.word word) } := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  exact support.actual.returned_capture sourceAt applied

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalInvocation
/-! Actual nullary public calls consume the existing captured closure and its
current history. Source argument packing is inverted at the genuine zero arity. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedLocal
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
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
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

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured lexical local. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
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


end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedLocalPublicExecution
/-! Actual make(10) initializes a lexical local and exports a closure over that
cell. Two direct calls consume the original handle and each current returned
session, with independent Source applications and complete retained histories. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ObservedInvocation factory.completion.session factory.handle
  second : ObservedInvocation first.completion.session factory.handle

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeInvocation factory.completion.session factory.handle
  let second ← observeInvocation first.completion.session factory.handle
  return ⟨factory, first, second⟩

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (entry : Entry) (function : Dynamic.Closure),
      entry.sourceType = .function .unit .word ∧ entry.handle = sequence.factory.handle ∧
      entry.source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      BinderExtends support.actual.header.function.source.owner support.actual.header.context
        observed.localBinder function.context ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        (∃ location, Dynamic.Environment.LooksUp function.captured observed.localBinder.id location ∧
          Dynamic.Heap.Reads initial.heap location { type := .word, value := some (.word seed) }) ∧
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source (.value (.word seed)) final.heap

/-- The static lexical tree and closure family come from the actual accepted
program. The factory allocation and both direct calls share one retained history. -/
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
  obtain ⟨function, source, parameters, result, extended, location, capture, cell⟩ := factoryTrace.make_capture
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType source parameters handle handleType
    sequence.first sequence.first.returned scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType source parameters handle handleType
    sequence.second sequence.second.returned scope
  exact ⟨support, entry, function, entryType, handle, source, parameters, result, extended,
    initial, first, final, ⟨location, capture, cell⟩, factoryTrace, firstTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed stages sequence receiver
  IO.println "Actual lexical capture: initialized local, repeated results 10/10, Source applications and returned histories proved"

end Tests.SourceCoreCapturedLocal
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics

structure FactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
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
  lambda : expression.form = .lambda [] .word [innerReturn.id]
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
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      · rw [shape.readRequirements, shape.readCoercions, shape.readType]
        exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have expressionTyped : ExpressionHasType function.typedBody lexical shape.expression.id
        (.function .unit .word) := by
      rw [← shape.expressionType]
      refine .intro (lookupExpression?_sound shape.expressionFound)
        (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
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
    "function make(seed: Word) returns (function() returns (Word)) { return lam() { return seed; }; } function read(f: function() returns (Word)) returns (Word) { return f(); }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

private def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (FactoryShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "captured factory input shape")
  let [Node.expression read, Node.statement innerReturn,
      Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "captured factory occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "captured factory parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "captured factory inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.function .unit .word]) "captured factory returns"
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
  let ⟨lambda⟩ ← observed (expression.form = .lambda [] .word [innerReturn.id]) "captured factory lambda"
  let ⟨expressionRaw⟩ ← observed (expression.rawType = .function .unit .word) "captured factory expressionRaw"
  let ⟨expressionType⟩ ← observed (expression.type = .function .unit .word) "captured factory expressionType"
  let ⟨requirements⟩ ← observed (expression.requirements = []) "captured factory requirements"
  let ⟨coercions⟩ ← observed (expression.coercions = []) "captured factory coercions"
  let ⟨returnStatement⟩ ← observed (statement.form = .returnStmt (some expression.id)) "captured factory returnStatement"
  let ⟨statementType⟩ ← observed (statement.type = .function .unit .word) "captured factory statementType"
  return { binder, read, innerReturn, expression, statement, parameters, inputTypes, returns, inputs, binderRequirements, roots, readFound, innerReturnFound, expressionFound, statementFound, readForm, readRaw, readType, readRequirements, readCoercions, innerReturnForm, innerReturnType, lambda, expressionRaw, expressionType, requirements, coercions, returnStatement, statementType }


structure ReadShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  callee : ExpressionNode
  call : ExpressionNode
  statement : StatementNode
  metadata : IndirectCallResolution
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.function .unit .word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  calleeFound : function.typedBody.lookupExpression? callee.id = some callee
  callFound : function.typedBody.lookupExpression? call.id = some call
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  calleeForm : callee.form = .reference binder.name (.local binder.id)
  calleeRaw : callee.rawType = .function .unit .word
  calleeType : callee.type = .function .unit .word
  calleeRequirements : callee.requirements = []
  calleeCoercions : callee.coercions = []
  callForm : call.form = .call callee.id [] (.indirect metadata)
  callRaw : call.rawType = .word
  callType : call.type = .word
  callRequirements : call.requirements = []
  callCoercions : call.coercions = []
  application : metadata = ⟨0, .unit, .unit, []⟩
  statementForm : statement.form = .returnStmt (some call.id)
  statementType : statement.type = .word

/-- The original local function scheme and exact empty call metadata give a
full declarative indirect-call derivation under any genuine input extension. -/
theorem ReadShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : ReadShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .word, hasValue := true, sawReturn := true, control := .returned }
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
    have callable : TypeAdmissible lexical (.function .unit .word) :=
      ⟨binders, .function (.builtin .unit) (.builtin .word)⟩
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder (.function .unit .word) [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible callable) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply (.function .unit .word)
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]
        exact .nil
    have calleeTyped : ExpressionHasType function.typedBody lexical shape.callee.id (.function .unit .word) := by
      rw [← shape.calleeType]
      refine .intro (lookupExpression?_sound shape.calleeFound)
        (shape.calleeForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.calleeRaw callable (shape.calleeType ▸ callable) ?_
      rw [shape.calleeRequirements, shape.calleeCoercions, shape.calleeType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    have application : IndirectApplicationValid lexical shape.metadata [] .unit := by
      rw [shape.application]
      exact .intro rfl rfl rfl (.nil _)
    have callTyped : ExpressionHasType function.typedBody lexical shape.call.id .word := by
      rw [← shape.callType]
      refine .intro (lookupExpression?_sound shape.callFound)
        (shape.callForm ▸ ExpressionFormHasRawType.indirectCall calleeTyped (.nil _) application)
        shape.callRaw word (shape.callType ▸ word) ?_
      rw [shape.callRequirements, shape.callCoercions, shape.callType, shape.application]
      exact .indirectCall (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm callTyped shape.statementType)⟩

private def readShape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (ReadShape function signature) := do
  let [binder] := function.typedBody.inputs
    | throw (IO.userError "read function input shape")
  let [Node.expression callee, Node.expression call, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "read function occurrence shape")
  let .call _ _ (.indirect metadata) := call.form
    | throw (IO.userError "read function indirect call")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "read function parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.function .unit .word]) "read function inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "read function returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "read function inputs"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "read function binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "read function roots"
  let ⟨calleeFound⟩ ← observed (function.typedBody.lookupExpression? callee.id = some callee) "read function calleeFound"
  let ⟨callFound⟩ ← observed (function.typedBody.lookupExpression? call.id = some call) "read function callFound"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "read function statementFound"
  let ⟨calleeForm⟩ ← observed (callee.form = .reference binder.name (.local binder.id)) "read function calleeForm"
  let ⟨calleeRaw⟩ ← observed (callee.rawType = .function .unit .word) "read function calleeRaw"
  let ⟨calleeType⟩ ← observed (callee.type = .function .unit .word) "read function calleeType"
  let ⟨calleeRequirements⟩ ← observed (callee.requirements = []) "read function calleeRequirements"
  let ⟨calleeCoercions⟩ ← observed (callee.coercions = []) "read function calleeCoercions"
  let ⟨callForm⟩ ← observed (call.form = .call callee.id [] (.indirect metadata)) "read function callForm"
  let ⟨callRaw⟩ ← observed (call.rawType = .word) "read function callRaw"
  let ⟨callType⟩ ← observed (call.type = .word) "read function callType"
  let ⟨callRequirements⟩ ← observed (call.requirements = []) "read function callRequirements"
  let ⟨callCoercions⟩ ← observed (call.coercions = []) "read function callCoercions"
  let ⟨application⟩ ← observed (metadata = ⟨0, .unit, .unit, []⟩) "read function application"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.id)) "read function statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "read function statementType"
  return {
    binder := binder
    callee := callee
    call := call
    statement := statement
    metadata := metadata
    parameters := parameters
    inputTypes := inputTypes
    returns := returns
    inputs := inputs
    binderRequirements := binderRequirements
    roots := roots
    calleeFound := calleeFound
    callFound := callFound
    statementFound := statementFound
    calleeForm := calleeForm
    calleeRaw := calleeRaw
    calleeType := calleeType
    calleeRequirements := calleeRequirements
    calleeCoercions := calleeCoercions
    callForm := callForm
    callRaw := callRaw
    callType := callType
    callRequirements := callRequirements
    callCoercions := callCoercions
    application := application
    statementForm := statementForm
    statementType := statementType
  }


structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  makeFunction : CheckedFunction
  readFunction : CheckedFunction
  makeSignature : ProgramFunctionSignature
  readSignature : ProgramFunctionSignature
  functions : program.functions = [makeFunction, readFunction]
  signatures : program.signatures.functions = [makeSignature, readSignature]
  methods : program.methods = []
  makeDeclaration : makeFunction.declaration = makeSignature.id
  readDeclaration : readFunction.declaration = readSignature.id
  distinct : makeSignature.id ≠ readSignature.id
  makeShape : FactoryShape makeFunction makeSignature
  readShape : ReadShape readFunction readSignature
  makeNodes : makeFunction.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  readNodes : readFunction.typedBody.nodes = [.expression readShape.callee,
    .expression readShape.call, .statement readShape.statement]

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [makeFunction, readFunction], [makeSignature, readSignature] =>
      let makeShape ← shape makeFunction makeSignature
      let readShape ← readShape readFunction readSignature
      let ⟨methods⟩ ← observed (program.methods = []) "unexpected methods"
      let ⟨makeDeclaration⟩ ← observed (makeFunction.declaration = makeSignature.id) "make declaration"
      let ⟨readDeclaration⟩ ← observed (readFunction.declaration = readSignature.id) "read declaration"
      let ⟨distinct⟩ ← observed (makeSignature.id ≠ readSignature.id) "distinct declarations"
      let ⟨makeNodes⟩ ← observed (makeFunction.typedBody.nodes = [.expression makeShape.read,
        .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "make complete source"
      let ⟨readNodes⟩ ← observed (readFunction.typedBody.nodes = [.expression readShape.callee,
        .expression readShape.call, .statement readShape.statement]) "read complete source"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
          · exact makeShape.statementTyping program.signatures
          · exact False.elim (distinct (makeDeclaration.symm.trans identity))
          · exact False.elim (distinct (identity.symm.trans readDeclaration))
          · exact readShape.statementTyping program.signatures
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
        makeFunction, readFunction, makeSignature, readSignature, functions, signatures, methods,
        makeDeclaration, readDeclaration, distinct, makeShape, readShape, makeNodes, readNodes⟩
    | _, _ => throw (IO.userError "captured reuse declaration count")
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
  let seeds := [SourceCompiler.Seed.declaration checked.makeSignature.id,
    SourceCompiler.Seed.declaration checked.readSignature.id]
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



/-- Each observation refers to an actual compiler row, unique physical slot,
entry, and original source declaration. No semantic body certificate is supplied. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  parameters : row.parameterSubstitution = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨parameters⟩ ← observed (row.parameterSubstitution = []) "reuse substitution"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.key)) with
      | none => throw (IO.userError "reuse entry missing")
      | some entry =>
        let ⟨entryKey⟩ ← observed (entry.key = row.key) "reuse entry key"
        return {
          row := row
          member := List.mem_of_find?_eq_some found
          sourceOwner := sourceOwner
          parameters := parameters
          ordinary := ordinary
          inputsOrdinary := by
            intro binder member
            have selected := List.all_eq_true.mp ordinaryInputs binder member
            cases same : binder.comptime <;> simp_all
          target := target
          global := global
          index := index
          slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
          globalKey := globalKey
          entry := entry
          entryMember := List.mem_of_find?_eq_some entryFound
          entryKey := entryKey }
    | _ => throw (IO.userError "reuse unique global slot")

structure ObservedProgram (fixture : CompiledFixture) where
  makeRow : ObservedRow fixture fixture.makeSignature
  readRow : ObservedRow fixture fixture.readSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 2
  distinctSlots : makeRow.index ≠ readRow.index
  makeShape : FactoryShape makeRow.row.function fixture.makeSignature
  readShape : ReadShape readRow.row.function fixture.readSignature
  makeNodes : makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]
  readNodes : readRow.row.function.typedBody.nodes = [.expression readShape.callee,
    .expression readShape.call, .statement readShape.statement]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let makeRow ← observeRow fixture fixture.makeSignature
  let readRow ← observeRow fixture fixture.readSignature
  let makeShape ← shape makeRow.row.function fixture.makeSignature
  let readShape ← readShape readRow.row.function fixture.readSignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 2) "reuse global count"
  let ⟨distinctSlots⟩ ← observed (makeRow.index ≠ readRow.index) "reuse distinct slots"
  let ⟨makeNodes⟩ ← observed (makeRow.row.function.typedBody.nodes = [.expression makeShape.read,
    .statement makeShape.innerReturn, .expression makeShape.expression, .statement makeShape.statement]) "reuse make nodes"
  let ⟨readNodes⟩ ← observed (readRow.row.function.typedBody.nodes = [.expression readShape.callee,
    .expression readShape.call, .statement readShape.statement]) "reuse read nodes"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "reuse local catalog"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "reuse callable profile"
  return {
    makeRow := makeRow
    readRow := readRow
    globalsLength := globalsLength
    distinctSlots := distinctSlots
    makeShape := makeShape
    readShape := readShape
    makeNodes := makeNodes
    readNodes := readNodes
    noLocals := noLocals
    profile := profile }


/-- The actual unique global slot identifies the complete prepared signature
and index, without choosing a new prepared row. -/
theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

/-- Issue exactly one authentic Header with its matching diagnostic receipt. -/
theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧
        actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    simp only [observed.parameters, SourceSemantics.ParameterSubstitution.RangeWellFormed,
      List.not_mem_nil, false_implies, implies_true]
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation observed.row =
      CallableNamedMetadata.instantiation observed.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, observed.parameters]
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by
      rw [metadata, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]
      exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

/-- Both real issuer packets cover every physical global slot. -/
theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (makeInput readInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      makeInput.row = observed.makeRow.row ∧ readInput.row = observed.readRow.row ∧
      ∃ (makePacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued makeInput)
        (readPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued readInput),
      ∃ (makeHeader : ActualHeader fixture observed.makeRow.row)
        (readHeader : ActualHeader fixture observed.readRow.row),
        makeHeader.header = makePacket.header ∧ readHeader.header = readPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons makePacket (.cons readPacket .nil))) := by
  obtain ⟨makeInput, makeRow, makePacket, makeHeader, makeEq, makeSlot, makeSignature⟩ := observed.makeRow.issue
  obtain ⟨readInput, readRow, readPacket, readHeader, readEq, readSlot, readSignature⟩ := observed.readRow.issue
  refine ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket, makeHeader, readHeader,
    makeEq, readEq, ?_⟩
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.readRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.readRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · refine ⟨makeHeader.header, ?_, makeSlot.trans same.symm, ?_⟩
    · rw [makeEq]; exact .head _
    · rw [same, observed.makeRow.slot.selected] at found
      exact makeSignature.trans (Option.some.inj found)
  · refine ⟨readHeader.header, ?_, readSlot.trans same.symm, ?_⟩
    · rw [readEq]; exact .tail _ (.head _)
    · rw [same, observed.readRow.slot.selected] at found
      exact readSignature.trans (Option.some.inj found)


structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


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

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 10

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its exported handle is not manufactured. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
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

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
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


/-- The complete checked read body contains no anonymous function occurrence. -/
theorem ObservedProgram.read_no_lambda {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.readRow.row.function.typedBody id node →
      ∀ parameters result body, node.form ≠ .lambda parameters result body := by
  intro id node present parameters result body form
  have member := present.1
  rw [observed.readNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have same := Node.expression.inj same
    rw [same, observed.readShape.calleeForm] at form
    cases form
  · rcases List.mem_cons.mp rest with same | rest
    · have same := Node.expression.inj same
      rw [same, observed.readShape.callForm] at form
      cases form
    · rcases List.mem_cons.mp rest with impossible | empty
      · cases impossible
      · cases empty

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseMakeSupport
/-! Concrete make support and the complete closure family for the two-function
checked program. The actual compiler observations produce every body premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering

structure ObservedMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  owned : observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    observed.makeRow.row.function.typedBody observed.makeShape.expression.id = .ok (observed.makeShape.expression, reported)
  binderScheme : observed.makeShape.binder.scheme = .mono .word

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) := do
  if accepted : proposition then return ⟨accepted⟩
  else throw (IO.userError label)

def observeMake (fixture : CompiledFixture) (observed : ObservedProgram fixture) : IO (ObservedMake fixture observed) := do
  let ⟨owned⟩ ← confirm (observed.makeShape.expression.id.occurrence.owner = observed.makeRow.row.function.typedBody.owner) "reuse lambda owner"
  let ⟨binderScheme⟩ ← confirm (observed.makeShape.binder.scheme = .mono .word) "reuse seed type"
  match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
      observed.makeRow.row.function.typedBody observed.makeShape.expression.id with
  | .error error => throw (IO.userError (reprStr error))
  | .ok (node, reported) =>
    let ⟨same⟩ ← confirm (node = observed.makeShape.expression) "reuse exact lambda read"
    return ⟨owned, reported, by simpa only [same] using read, binderScheme⟩

theorem ActualHeader.make_formation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedReturnLambdaFormation.of_terminal terminal
    fixture.recipePrepared diagnostic fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.makeRow.entryMember
    (node := observed.makeShape.expression) (reported := extra.reported)
  · rw [actual.source, expression]; exact observed.makeShape.expressionFound
  · exact observed.makeShape.lambda
  · rw [actual.source, expression]; exact extra.owned
  · exact observed.makeShape.requirements
  · exact observed.makeShape.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact extra.read
  · rw [actual.source]; exact observed.makeShape.innerReturnFound
  · exact observed.makeShape.innerReturnForm
  · exact observed.makeShape.innerReturnType

theorem ActualHeader.make_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (stages : ObservedStages fixture observed.makeRow)
    (actual : ActualHeader fixture observed.makeRow.row)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.makeShape.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.make_formation extra stages terminal diagnostic expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual headers
    (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point complete
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.makeRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.readRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have makeBound := (List.getElem?_eq_some_iff.mp observed.makeRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.readRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  have casesIndex : index = observed.makeRow.index ∨ index = observed.readRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.makeRow.prepared_slot makeHeader.prepared).2
    rw [same, ← actualIndex, makeHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) makeHeader.prepared.same
  · right
    have actualIndex := (observed.readRow.prepared_slot readHeader.prepared).2
    rw [same, ← actualIndex, readHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) readHeader.prepared.same

theorem ObservedProgram.make_lambda_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {body : List StatementId}
    (found : observed.makeRow.row.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body) :
    parameters = [] ∧ result = .word ∧ body = [observed.makeShape.innerReturn.id] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.makeNodes] at member
  rcases List.mem_cons.mp member with same | rest
  · have nodeEq := Node.expression.inj same
    rw [nodeEq, observed.makeShape.readForm] at form
    cases form
  · rcases List.mem_cons.mp rest with impossible | rest
    · cases impossible
    · rcases List.mem_cons.mp rest with same | rest
      · have nodeEq := Node.expression.inj same
        rw [nodeEq, observed.makeShape.lambda] at form
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

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source makeHeader readHeader support.caller.selected with original | original
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.read_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence stagePrepared code support provenance
      receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.makeNodes) observed.makeShape.lambda bodyShape
      (by rw [sameSource]; exact observed.makeShape.innerReturnFound) observed.makeShape.innerReturnForm
      (by rw [sameSource]; exact observed.makeShape.readFound) observed.makeShape.readForm
      observed.makeShape.readRequirements observed.makeShape.readCoercions observed.noLocals
      fixture.makeSignature (by rw [fixture.sameProgram, fixture.signatures]; exact .head _)
      (by rw [sameSource]; exact observed.makeRow.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)


theorem ActualHeader.make_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (extra : ObservedMake fixture observed) (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.makeShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    extra.binderScheme, TypeSystem.Scheme.mono] using inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseReadSupport
/-! The observed read(f) program supplies its entire named body support from
its two actual expression rows. No call readiness, Source execution or payload
representation is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

private theorem read_expression {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) {id : ExpressionId} {node : ExpressionNode}
    (found : observed.readRow.row.function.typedBody.lookupExpression? id = some node) :
    node = observed.readShape.callee ∨ node = observed.readShape.call := by
  have present := (lookupExpression?_sound found).1
  rw [observed.readNodes] at present
  rcases List.mem_cons.mp present with same | rest
  · exact Or.inl (Node.expression.inj same)
  · rcases List.mem_cons.mp rest with same | rest
    · exact Or.inr (Node.expression.inj same)
    · rcases List.mem_cons.mp rest with impossible | empty
      · cases impossible
      · cases empty

/-- Empty local catalogs and the complete original occurrence table establish
all metadata exclusions in the recursive caller grammar. -/
theorem ActualHeader.read_metadata {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same]; exact observed.readShape.calleeRequirements
    · rw [same]; exact observed.readShape.callRequirements
  · intro id _ node found
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same]; exact observed.readShape.calleeCoercions
    · rw [same]; exact observed.readShape.callCoercions
  · intro id _
    simp only [observed.noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rcases read_expression observed found with same | same
    · rw [same, observed.readShape.calleeForm] at form
      cases form
    · rw [same, observed.readShape.callForm] at form
      cases form
      rw [observed.readShape.application]
  · intro id _ node found name binder form
    simp only [observed.noLocals, List.any_nil]

/-- The exact terminal call has one local-read child and no argument children. -/
theorem ActualHeader.read_syntax {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source observed.readShape.call.id := by
  rw [actual.source]
  exact .call observed.readShape.callFound observed.readShape.callForm
    (.leaf (.read observed.readShape.calleeFound observed.readShape.calleeForm))
    (by intro id member; cases member)

/-- All finite metadata, original typing and selected scope premises of the
compiler producer are derived from this concrete checked/compiled fixture. -/
theorem ActualHeader.read_support_at {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (expression : terminal.expression = observed.readShape.call.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
      actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed (ActualHeader.read_metadata observed actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.read_syntax observed actual) stagePrepared point

/-- The actual terminal lowering supplies its own Point certificate and
preparation packet before the concrete support producer is invoked. -/
theorem ActualHeader.read_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.readRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.readShape.call.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal observed.readShape.call.id
    observed.readShape.statement observed.readShape.roots observed.readShape.statementFound observed.readShape.statementForm
  exact ⟨terminal, expression, ActualHeader.read_support_at observed actual terminal diagnostic expression point receiver stagePrepared⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseSequence
/-! Actual public calls reuse distinct closure exports through the returned
sessions. Every step retains its original startup and run receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
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

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  readFirst : ObservedCall second.completion.session observed.readRow.row.key [.function first.handle]
  firstValue : readFirst.completion.value = .word seed
  intervening : ObservedFunctionCall readFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  readSecond : ObservedCall intervening.completion.session observed.readRow.row.key [.function second.handle]
  secondValue : readSecond.completion.value = .word secondSeed
  readFirstAgain : ObservedCall readSecond.completion.session observed.readRow.row.key [.function first.handle]
  firstValueAgain : readFirstAgain.completion.value = .word seed

private def confirm_variant (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  let ⟨distinct⟩ ← confirm_variant (first.handle ≠ second.handle) "distinct captured closures reused the same handle"
  let readFirst ← observeCall second.completion.session observed.readRow.row.key [.function first.handle]
  let ⟨firstValue⟩ ← confirm_variant (readFirst.completion.value = .word seed) "first capture did not return 10"
  let intervening ← observeFunctionCall readFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  let readSecond ← observeCall intervening.completion.session observed.readRow.row.key [.function second.handle]
  let ⟨secondValue⟩ ← confirm_variant (readSecond.completion.value = .word secondSeed) "second capture did not return 20"
  let readFirstAgain ← observeCall readSecond.completion.session observed.readRow.row.key [.function first.handle]
  let ⟨firstValueAgain⟩ ← confirm_variant (readFirstAgain.completion.value = .word seed) "first capture changed after intervening calls"
  pure ⟨first, second, distinct, readFirst, firstValue, intervening, readSecond, secondValue,
    readFirstAgain, firstValueAgain⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedDirectSequence
/-! Actual direct public invocations retain each original checkpoint and receipt.
Separate closures are called after later factory allocations and prior invocations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedDirect
open Solcore Frontend SourceInference SourceSemantics
open Tests.SourceCoreCapturedReuse

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

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.makeRow
  second : ObservedFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  distinct : first.handle ≠ second.handle
  invokeFirst : ObservedInvocation second.completion.session first.handle
  firstValue : invokeFirst.completion.value = .word seed
  intervening : ObservedFunctionCall invokeFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  invokeSecond : ObservedInvocation intervening.completion.session second.handle
  secondValue : invokeSecond.completion.value = .word secondSeed
  invokeFirstAgain : ObservedInvocation invokeSecond.completion.session first.handle
  firstValueAgain : invokeFirstAgain.completion.value = .word seed

private def confirm (proposition : Prop) [Decidable proposition] (label : String) : IO (PLift proposition) :=
  if accepted : proposition then pure ⟨accepted⟩ else throw (IO.userError label)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.makeRow
  let second ← observeFunctionCall first.completion.session observed.makeRow.row.key [.word secondSeed]
  let ⟨distinct⟩ ← confirm (first.handle ≠ second.handle) "distinct direct closures reused the same handle"
  let invokeFirst ← observeInvocation second.completion.session first.handle
  let ⟨firstValue⟩ ← confirm (invokeFirst.completion.value = .word seed) "first direct capture did not return 10"
  let intervening ← observeFunctionCall invokeFirst.completion.session observed.makeRow.row.key [.word interveningSeed]
  let invokeSecond ← observeInvocation intervening.completion.session second.handle
  let ⟨secondValue⟩ ← confirm (invokeSecond.completion.value = .word secondSeed) "second direct capture did not return 20"
  let invokeFirstAgain ← observeInvocation invokeSecond.completion.session first.handle
  let ⟨firstValueAgain⟩ ← confirm (invokeFirstAgain.completion.value = .word seed) "first direct capture changed after intervening calls"
  pure ⟨first, second, distinct, invokeFirst, firstValue, intervening, invokeSecond, secondValue,
    invokeFirstAgain, firstValueAgain⟩

end Tests.SourceCoreCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseSupports
/-! A complete static package is produced from the actual two issuer packets.
The Type-valued terminal dispatcher branches only on real physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

private def selectTwo {compiled : SourceCoreUnifiedCompilation.Compiled}
    {left right : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (distinct : left.slot ≠ right.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (leftValue : property left) (rightValue : property right) :
    ∀ header, header ∈ [left, right] → property header := by
  intro header member
  if sameSlot : header.slot = left.slot then
    have same : header = left := by
      rcases List.mem_cons.mp member with same | rest
      · exact same
      · have same := List.mem_singleton.mp rest
        exact False.elim (distinct (sameSlot ▸ congrArg (·.slot) same))
    exact same.symm ▸ leftValue
  else
    have same : header = right := by
      rcases List.mem_cons.mp member with same | rest
      · exact False.elim (sameSlot (congrArg (·.slot) same))
      · exact List.mem_singleton.mp rest
    exact same.symm ▸ rightValue

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  makeInput : Input fixture.recipe.compiled
  readInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  readRow : readInput.row = observed.readRow.row
  makePacket : Issued makeInput
  readPacket : Issued readInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  readHeader : ActualHeader fixture observed.readRow.row
  makeEq : makeHeader.header = makePacket.header
  readEq : readHeader.header = readPacket.header
  rows : Inventory [makeInput, readInput]
  rowsEq : rows = .cons makePacket (.cons readPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, readInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot
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
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  readDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named readHeader.header.named.signature.key)

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket,
    makeHeader, readHeader, makeEq, readEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, readInput] := .cons makePacket (.cons readPacket .nil)
  have headerList : headers rows = [makeHeader.header, readHeader.header] := by
    simp only [rows, headers, makeEq, readEq]
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have readIndex : readHeader.header.slot = observed.readRow.index :=
    readHeader.aligned.slot.trans (observed.readRow.prepared_slot readHeader.prepared).2
  have slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot := by
    rw [makeIndex, readIndex]
    exact observed.distinctSlots
  have inputDistinct : makeInput.prepared.index ≠ readInput.prepared.index := by
    have left : makeHeader.header.slot = makeInput.prepared.index := by
      rw [makeEq]; exact makePacket.aligned.slot
    have right : readHeader.header.slot = readInput.prepared.index := by
      rw [readEq]; exact readPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.expression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨readTerminal, _readExpression, readSupport⟩ :=
    readHeader.read_support observed receiver (actualStagePrepared fixture)
  obtain ⟨readSupport⟩ := readSupport
  let property := fun header => Σ terminal : Terminal header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo slotsDistinct property
      ⟨makeTerminal, makeSupport⟩ ⟨readTerminal, .recursive readSupport⟩ header (headerList ▸ member)
  exact ⟨{
    makeInput := makeInput
    readInput := readInput
    makeRow := makeRow
    readRow := readRow
    makePacket := makePacket
    readPacket := readPacket
    makeHeader := makeHeader
    readHeader := readHeader
    makeEq := makeEq
    readEq := readEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family makeHeader readHeader (actualStagePrepared fixture) receiver association
    makeDescriptor := makeHeader.descriptor makeStages
    readDescriptor := readHeader.descriptor readStages }⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseCommon
/-! Concrete receiving diagnostics and retained state for the actual public
sequence. These records are constructed by public execution proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed
  executed : fixture.recipe.compiled.indexed.runSource observed.makeRow.row.key [.word seed]
    runOptions.executionFuel runOptions.inputValidationFuel = .ok completion

def observeReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedReceiver fixture observed) := do
  match executed : fixture.recipe.compiled.indexed.runSource observed.makeRow.row.key [.word seed]
      runOptions.executionFuel runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok completion => return ⟨completion, executed⟩

abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
    support.makeHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.makeHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedDirectInvocation
/-! A direct public invocation consumes the actual retained Source closure and
returns its existing history at the real completed session and captured heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source [] outcome after

theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨nativeAt, heaps, stable, heapTyped, entriesAt⟩ := state.history.current
  obtain ⟨imported, represented, sourceTyped⟩ := entriesAt entry member
  rw [entryType, entryHandle] at imported
  rw [entryType, entrySource] at represented sourceTyped
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate
    support.makeHeader.header fixture.source_wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      support.makeHeader.header.function.context support.makeHeader.header.function.source := by
    rw [support.makeHeader.header.frame.context, support.makeHeader.header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  obtain ⟨checkpoint, actual, generation, value, finalStore, nativeResult, sourceSize, outcome,
      after, finalMap, finalWorld, started, succeeded, actualAt, projected, requested, _payloadType,
      trace, result⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.public_invoke_succeeded_reflects_unit
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (stagePrepared := actualStagePrepared fixture) (profile := observed.profile)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (caller := state.caller) (stable := stable)
      (runtime := runtime) (heapTyped := heapTyped) (calleeTyped := sourceTyped)
      (calleeRelated := represented) (parameters := parameters) (heaps := heaps)
      (prepared := fixture.recipePrepared) (atRecipe := state.atRecipe) (nativeAt := nativeAt)
      (handleType := handleType) (imported := imported) state.atSession call.executed invocation
  have nativeResultEq : nativeResult = .word := (Except.ok.inj projected).symm
  rw [nativeResultEq] at result
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested
    (actualAt.1.symm.trans returned) result.1
  obtain ⟨reached, _related, retained⟩ := state.history.after_packed_success started succeeded result
  have registry := started.returned_registry succeeded
  rw [started.simple_registry .unit, state.registry] at registry
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      actualAt.2.2.2, state.atRecipe, registry, retained⟩
  refine ⟨next, sourceSize, ?_⟩
  simpa only [entrySource, outcomeValue] using trace

end Tests.SourceCoreCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseSelection
/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.makeRow.row.key ≠ observed.readRow.row.key := by
  intro same
  have globals : observed.makeRow.global.key = observed.readRow.global.key :=
    observed.makeRow.globalKey.trans (same.trans observed.readRow.globalKey.symm)
  exact observed.distinctSlots (observed.makeRow.slot.unique observed.readRow.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_make_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, readHeader.header] root header)
    (key : root.key = observed.makeRow.row.key) : header = makeHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, readHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_read_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (readHeader : ActualHeader fixture observed.readRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [makeHeader.header, readHeader.header] root header)
    (key : root.key = observed.readRow.row.key) : header = readHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, makeHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey)
  · exact List.mem_singleton.mp rest

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (makeHeader : ActualHeader fixture observed.makeRow.row)
  (readHeader : ActualHeader fixture observed.readRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_make (request : Started [makeHeader.header, readHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.makeRow.row.key arguments fuel world store) :
    request.header = makeHeader.header :=
  selected_make_root makeHeader readHeader request.selected (started_key request)

theorem selected_read (request : Started [makeHeader.header, readHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.readRow.row.key arguments fuel world store) :
    request.header = readHeader.header :=
  selected_read_root makeHeader readHeader request.selected (started_key request)

theorem selected_make_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, readHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.makeRow.row.key arguments fuel world store) : request.header = makeHeader.header := by
  subst headers
  exact selected_make makeHeader readHeader request

theorem selected_read_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [makeHeader.header, readHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.readRow.row.key arguments fuel world store) : request.header = readHeader.header := by
  subst headers
  exact selected_read makeHeader readHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.makeHeader.header, support.readHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.makeEq, support.readEq]


private theorem parameter_nil (type : TypeSystem.Ty) :
    TypeSystem.ParameterSubstitution.apply [] type = type := by
  induction type <;> simp_all [TypeSystem.ParameterSubstitution.apply,
    TypeSystem.ParameterSubstitution.lookup?]

theorem ObservedRow.source_types {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (signatureMember : signature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions)
    (actual : ActualHeader fixture observed.row) :
    observed.row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = signature.parameterTypes ∧
      observed.row.function.inferredBodyType = TypeSystem.Ty.productMany signature.returnTypes := by
  obtain ⟨request, original, generic, originalMember, genericMember, _, accepted⟩ := actual.prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have body := RecursiveNamedSpecializationBodyFacts.body accepted
  have owner := congrArg (fun source => source.owner) body
  change observed.row.function.typedBody.owner = generic.typedBody.owner at owner
  have originalEq : original = signature :=
    eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids originalMember signatureMember
      (identities.1.trans (identities.2.1.symm.trans (owner.symm.trans observed.sourceOwner)))
  subst original
  have valid := fixture.source_wellFormed.functions_valid (FunctionDefinition.ofChecked generic)
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩)
  cases valid with
  | @intro typedSignature facts typedMember typedOwner bodyValid =>
    have same : typedSignature = signature :=
      eq_of_mem_of_nodup_map fixture.source_wellFormed.signatures.function_ids typedMember signatureMember
        (typedOwner.symm.trans identities.1.symm)
    subst typedSignature
    cases bodyValid with
    | intro _ _ _ _ _ result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      have fields := (CallableCoercionBodyProvenance.specialization_fields accepted).1
      rw [fields, observed.parameters]
      simp only [SourceSpecialization.applyCheckedFunction, SourceSpecialization.applyTypedSource,
        List.map_map, Function.comp_def, SourceSpecialization.applyBinder,
        SourceSpecialization.applyScheme, parameter_nil]
      exact ⟨inputs, result⟩

theorem ActualHeader.read_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.function .unit .word] := by
  have raw := (observed.readRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.readShape.inputTypes] at raw
  rw [← actual.source] at raw
  rw [actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.read_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) : actual.header.types = [.function .unit .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  have raw := actual.read_input_types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans raw

theorem ActualHeader.read_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.readRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.readShape.returns]
  rfl

theorem ActualHeader.make_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.makeRow.row) :
    actual.header.function.resultType = .function .unit .word := by
  have result := (observed.makeRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.makeShape.returns]
  rfl

theorem ActualHeader.read_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.readRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.read_result_type] at projected
  exact (Except.ok.inj projected).symm

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseClosureShape
/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
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
    {value : Dynamic.Value} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda [] .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ function : Dynamic.Closure,
      value = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
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
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {word : Core.Word} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation before [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  have parameters : support.makeHeader.header.function.parameters = [observed.makeShape.binder] := by
    rw [support.makeHeader.header.parameters, ← support.makeHeader.header.inputs,
      support.makeHeader.source, observed.makeShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, _allocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ support.makeHeader.header.unique
  have bodyEq : support.makeHeader.header.function.body = [observed.makeShape.statement.id] := by
    apply statement_roots_injective
    rw [← support.makeHeader.header.agreement.roots, support.makeHeader.source, observed.makeShape.roots]
    rfl
  have statementFound : child.source.lookupStatement? observed.makeShape.statement.id =
      some observed.makeShape.statement := by
    rw [sourceEq, support.makeHeader.source]
    exact observed.makeShape.statementFound
  have expressionFound : child.source.lookupExpression? observed.makeShape.expression.id =
      some observed.makeShape.expression := by
    rw [sourceEq, support.makeHeader.source]
    exact observed.makeShape.expressionFound
  rw [support.makeHeader.make_result_type] at converted
  cases converted
  rw [bodyEq] at body
  exact lambda_shape unique expressionFound observed.makeShape.lambda observed.makeShape.coercions
    (returned_expression unique statementFound observed.makeShape.returnStatement body)

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseMakeStep
/-! A genuine successful public factory call extends the current retained
history with its actual new closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public make call constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.make_typed_handle
    (extra : ObservedMake fixture observed)
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.readInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selected := selected_make_at support.makeHeader support.readHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word] [.word word] := by
    rw [selected, support.makeHeader.make_input_types extra]
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
    exact support.makeDescriptor
  obtain ⟨actual, generation, nativeValue, finalStore, capture,
    sourceSize, outcome, heap, mapping, world, succeeded, valueEq, typeEq, budgetEq,
    returnedAt, trace, result, caller, source, payload, sourceValue, nativePayload, related, continued⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_remembers
      (inputs := [support.makeInput, support.readInput]) (rows := support.rows)
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
  rw [resultType, selected, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans call.returned)
  refine ⟨entry, ?_, rfl, handleType, after, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · change request.header.function.resultType = .function .unit .word
    rw [selected]
    exact support.makeHeader.make_result_type
  · exact selected ▸ request.sourceAt
  · simpa only [entry, after, sourceValue] using trace

/-- Preserve the original continuation API for clients that only need the
Source value and the new retained history. -/
theorem RetainedState.make
    (extra : ObservedMake fixture observed)
    (state : RetainedState support publicSession entries)
    {word : Core.Word}
    (call : ObservedFunctionCall publicSession observed.makeRow.row.key [.word word])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.makeHeader.header invocation state.heap [.word word]
          (.value entry.source) after.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, after, trace⟩ :=
    state.make_typed_handle extra call invocation
  exact ⟨entry, sourceType, handle, after, trace⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseReadStep
/-! A retained closure is passed to the actual read function. Its successful
public Word result identifies the independent Source result and returns the
same finite history at the new actual session and heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem RetainedState.read {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (call : ObservedCall publicSession observed.readRow.row.key [.function handle])
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support support.readHeader.header invocation state.heap [entry.source]
        (.value (.word word)) after.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.readInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.readHeader.header :=
    selected_read_at support.makeHeader support.readHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.function handle] [entry.source] := by
    rw [selectedHeader, support.readHeader.read_input_types, ← entryType, ← entryHandle]
    exact .cons (.retained entry member) .nil
  have registry := request.started.function_registry state.registry
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiver.completion.result.context.registry := by
    rw [registry]
    exact receiver.completion.result.extension
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]
    exact support.readDescriptor
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.makeInput, support.readInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (observations := support.observations)
      (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := fun header member =>
        CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (support.terminals header member)) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have requested := request.started.original.result_type_at
    (show state.artifact.RecipeAt fixture.recipe from by
      have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
          RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
        fun artifact _ atRecipe => by cases artifact; exact atRecipe
      exact convert _ _ state.atRecipe)
    request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, selectedHeader, support.readHeader.read_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans returned)
    (by rw [selectedHeader]; exact support.readHeader.read_output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReuseSeed
/-! Actual initialization and the first public make(10) execution establish
the first Source closure and history entry, including its captured parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open RecursiveNamedPublicFunctionHistory (Entry)

theorem first_meaning_typed_handle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed) (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      first.handle.sourceType = .function .unit .word ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree fixture.recipe.compiled
      (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed))
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ :=
    fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    have same : value = .word seed := List.mem_singleton.mp member
    exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.makeHeader.header := by
    apply selected_make_root (fixture := fixture) (observed := observed)
      support.makeHeader support.readHeader (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.makeRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.makeHeader.header.function.context
      (support.makeHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [support.makeHeader.make_input_types extra]
    exact .cons (.leaf (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩)) .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.makeHeader.header support.makeInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.makePacket.header.named.specialized support.makeInput.prepared.available)) := by
    rw [support.makeEq]
    exact support.makePacket.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, _fullResult,
      returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [support.makeInput, support.readInput]) (rows := support.rows) (distinct := support.distinct)
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
      (invocation := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
      first.started first.executed first.returned support.makeDescriptor
  let entry : Entry := ⟨support.makeHeader.header.function.resultType, source, first.handle,
    payload, support.makeHeader.header.output, runOptions.outputValidationFuel⟩
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
  rw [resultType, support.makeHeader.make_result_type] at requested
  have handleType := succeeded.function_source_type requested (valueEq.symm.trans first.returned)
  refine ⟨entry, support.makeHeader.make_result_type, rfl, handleType, state, ?_⟩
  exact ⟨support.makeInput.prepared.available, _, sourceSize, sourceAt, sourceValue ▸ trace⟩

/-- The original factory theorem remains available when the public handle's
raw type is not needed by the caller. -/
theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (extra : ObservedMake fixture observed) (support : PublicSupports receiver)
    (makeStages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ entry : Entry,
      entry.sourceType = .function .unit .word ∧ entry.handle = first.handle ∧
      ∃ state : RetainedState support first.completion.session [entry],
        SourceCall support support.makeHeader.header
          (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
          ⟨[]⟩ [.word seed] (.value entry.source) state.heap := by
  obtain ⟨entry, sourceType, handle, _handleType, state, trace⟩ :=
    first_meaning_typed_handle extra support makeStages first
  exact ⟨entry, sourceType, handle, state, trace⟩

end Tests.SourceCoreCapturedReuse
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedDirectPublicExecution
/-! Three actual factory executions and three direct public handle invocations
retain distinct captures through intervening calls, with independent Source
applications and exact returned histories for the complete sequence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
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
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.makeHeader.header scope firstState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        SourceInvocation support scope secondState.heap first.source
          (.value (.word seed)) firstInvokedState.heap ∧
        SourceCall support support.makeHeader.header scope firstInvokedState.heap [.word interveningSeed]
          (.value intervening.source) interveningState.heap ∧
        SourceInvocation support scope interveningState.heap second.source
          (.value (.word secondSeed)) secondInvokedState.heap ∧
        SourceInvocation support scope secondInvokedState.heap first.source
          (.value (.word seed)) finalState.heap

/-- Every initial state, callable, capture, argument and result belongs to the
original actual public execution; semantic body laws are constructed internally. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, firstState, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    firstState.make_typed_handle extra sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨firstInvokedState, firstInvokedTrace⟩ := invoke secondState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirst sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstInvokedState.make_typed_handle extra sequence.intervening scope
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
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct closure reuse: six public calls, independent captures 10/20, intervening make(30), Source results and returned histories proved"

end Tests.SourceCoreCapturedDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreCapturedReusePublicExecution
/-! The actual checked two-function program connects six public executions to
independent Source applications and reusable histories. Distinct captures are
read after another factory invocation, then the first capture is read again. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedReuse
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let makeScope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    let readScope := RecursiveStageRegistry.scope readStages.sidecar [] support.readHeader.header.function
    ∃ first second intervening : Entry,
      first.sourceType = .function .unit .word ∧ second.sourceType = .function .unit .word ∧
      intervening.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ second.handle = sequence.second.handle ∧
      intervening.handle = sequence.intervening.handle ∧ first.handle ≠ second.handle ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, second],
      ∃ firstReadState : RetainedState support sequence.readFirst.completion.session [first, second],
      ∃ interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening],
      ∃ secondReadState : RetainedState support sequence.readSecond.completion.session [first, second, intervening],
      ∃ finalState : RetainedState support sequence.readFirstAgain.completion.session [first, second, intervening],
        SourceCall support support.makeHeader.header makeScope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.makeHeader.header makeScope firstState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        SourceCall support support.readHeader.header readScope secondState.heap [first.source]
          (.value (.word seed)) firstReadState.heap ∧
        SourceCall support support.makeHeader.header makeScope firstReadState.heap [.word interveningSeed]
          (.value intervening.source) interveningState.heap ∧
        SourceCall support support.readHeader.header readScope interveningState.heap [second.source]
          (.value (.word secondSeed)) secondReadState.heap ∧
        SourceCall support support.readHeader.header readScope secondReadState.heap [first.source]
          (.value (.word seed)) finalState.heap

/-- Every static support and dynamic history is built from the actual checker,
compiler, public startups and public execution receipts of this fixture. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages readStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let makeScope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  let readScope := RecursiveStageRegistry.scope readStages.sidecar [] support.readHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstState, firstTrace⟩ :=
    first_meaning extra support makeStages sequence.first
  obtain ⟨second, secondType, secondHandle, secondState, secondTrace⟩ :=
    firstState.make extra sequence.second makeScope
  obtain ⟨firstReadState, firstReadTrace⟩ := secondState.read first (by simp)
    firstType firstHandle sequence.readFirst sequence.firstValue readScope
  obtain ⟨intervening, interveningType, interveningHandle, interveningState, interveningTrace⟩ :=
    firstReadState.make extra sequence.intervening makeScope
  obtain ⟨secondReadState, secondReadTrace⟩ := interveningState.read second (by simp)
    secondType secondHandle sequence.readSecond sequence.secondValue readScope
  obtain ⟨finalState, finalTrace⟩ := secondReadState.read first (by simp)
    firstType firstHandle sequence.readFirstAgain sequence.firstValueAgain readScope
  refine ⟨support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, ?_, firstState, secondState, firstReadState,
    interveningState, secondReadState, finalState, firstTrace, secondTrace, firstReadTrace,
    interveningTrace, secondReadTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual captured closure reuse: six public calls, distinct captures 10/20, intervening make(30), Source Word results and retained histories proved"

end Tests.SourceCoreCapturedReuse
end
