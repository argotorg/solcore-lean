import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadLambdaMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryFailures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance
import Solcore.SourceSemantics.CoreLowering.RecursivePublicCallableArity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionSourceFailures
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionOutcomes
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes

/-!
# Lexical failure tests

Reads of uninitialized locals, from independent source typing through certified, selected and direct
failure outcomes.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureSource
/-! Independent Source typing of a real uninitialized local read and a
subsequent identity call. Runtime failure is established separately. -/

set_option autoImplicit false
set_option Elab.async false

namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics

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

structure FailedShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  declared : StatementNode
  read : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = []
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = []
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  binderOwner : binder.id.owner = function.typedBody.owner
  roots : function.typedBody.roots = [.statement declared.id, .statement statement.id]
  nodes : function.typedBody.nodes = [.statement declared, .expression read, .statement statement]
  declaredFound : function.typedBody.lookupStatement? declared.id = some declared
  declaredForm : declared.form = .letDecl binder none
  declaredType : declared.type = .unit
  readFound : function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.id)
  statementType : statement.type = .word

theorem FailedShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : FailedShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.declared.id, shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
  let letFacts : StatementFacts := {type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit}
  refine ⟨BodyFacts.cons letFacts (BodyFacts.singleton facts), rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension
  let lexical := checkedBodyContext signatures signature function
  have binders : TypeParameterBindersWellFormed lexical := by
    simp [TypeParameterBindersWellFormed, lexical, checkedBodyContext, declarationContext, Context.ofSignatures,
      Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements,
      Context.withResidualTypeVariables, shape.parameters]
  have word : TypeAdmissible lexical .word := ⟨binders, .builtin .word⟩
  let inner := lexical.withLocal shape.binder.id shape.binder.scheme shape.binder.schemeRequirements
  have extended : BinderExtends function.typedBody.owner lexical shape.binder inner := by
    apply BinderExtends.intro
    · exact {
        owned := shape.binderOwner
        scheme := shape.binderScheme.symm ▸ SchemeWellFormed.monoAdmissible word
        quantified_fresh := by rw [shape.binderScheme]; simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
        monomorphic_requirements_empty := fun _ => shape.binderRequirements }
    · simp [LocalFresh, lexical, checkedBodyContext, declarationContext, Context.ofSignatures,
        Context.forDeclaration, Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables]
  have innerWord : TypeAdmissible inner .word := ⟨binders, .builtin .word⟩
  have instantiation : LocalSchemeInstantiationValid inner shape.binder .word [] := by
    refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
      (shape.binderScheme.symm ▸ SchemeWellFormed.monoAdmissible innerWord) [] ?_ ?_ ?_ (by simp) ?_ ?_
    · simpa only [shape.binderScheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
    · intro metavariable replacement member; cases member
    · simpa only [shape.binderScheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
    · intro id member; cases member
    · rw [instantiateLocalSchemePredicates, shape.binderRequirements]; exact .nil
  have readTyped : ExpressionHasType function.typedBody inner shape.read.id .word := by
    rw [← shape.readType]
    refine .intro (lookupExpression?_sound shape.readFound)
      (shape.readForm ▸ ExpressionFormHasRawType.reference
        (.local extended.local_self extended.local_scheme_requirements_self instantiation))
      shape.readRaw innerWord (shape.readType ▸ innerWord) ?_
    rw [shape.readRequirements, shape.readCoercions, shape.readType]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  have declared : StatementHasType function.typedBody ⟨.word, 0⟩ lexical shape.declared.id inner letFacts := by
    apply StatementHasType.letUninitialized (lookupStatement?_sound shape.declaredFound) shape.declaredForm
    · rw [shape.binderScheme]; rfl
    · rw [shape.binderScheme]; rfl
    · exact extended
    · exact shape.declaredType
  exact ⟨_, .cons declared (.singleton (.returnValue (lookupStatement?_sound shape.statementFound)
    shape.statementForm readTyped shape.statementType))⟩

structure IdentityShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  binder : TypedBinder
  read : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [.word]
  returns : signature.returnTypes = [.word]
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono .word
  binderRequirements : binder.schemeRequirements = []
  binderOrdinary : binder.comptime = false
  roots : function.typedBody.roots = [.statement statement.id]
  nodes : function.typedBody.nodes = [.expression read, .statement statement]
  readFound : function.typedBody.lookupExpression? read.id = some read
  readForm : read.form = .reference binder.name (.local binder.id)
  readRaw : read.rawType = .word
  readType : read.type = .word
  readRequirements : read.requirements = []
  readCoercions : read.coercions = []
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.id)
  statementType : statement.type = .word

theorem IdentityShape.statementTyping {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : IdentityShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .word, hasValue := true, sawReturn := true, control := .returned}
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
    have instantiation : LocalSchemeInstantiationValid lexical shape.binder .word [] := by
      refine .intro (LocalSchemeRequirementsWellFormed.empty _ _ shape.binderRequirements)
        (scheme.symm ▸ SchemeWellFormed.monoAdmissible word) [] ?_ ?_ ?_ (by simp) ?_ ?_
      · simpa only [scheme, TypeSystem.Scheme.mono] using ExactSubstitution.empty
      · intro metavariable replacement member; cases member
      · simpa only [scheme, TypeSystem.Scheme.mono] using SchemeInstantiates.empty_apply .word
      · intro id member; cases member
      · rw [instantiateLocalSchemePredicates, shape.binderRequirements]; exact .nil
    have readTyped : ExpressionHasType function.typedBody lexical shape.read.id .word := by
      rw [← shape.readType]
      refine .intro (lookupExpression?_sound shape.readFound)
        (shape.readForm ▸ ExpressionFormHasRawType.reference
          (.local head.local_self head.local_scheme_requirements_self instantiation))
        shape.readRaw word (shape.readType ▸ word) ?_
      rw [shape.readRequirements, shape.readCoercions, shape.readType]
      exact .ordinary (by intro id member; cases member) (.nil _) rfl
    exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
      shape.statementForm readTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function failed() returns (Word) { let local: Word; return local; } function identity(seed: Word) returns (Word) { return seed; }"}] }

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeFailed (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (FailedShape function signature) := do
  let [Node.statement declared, Node.expression read, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "failed occurrence shape")
  let .letDecl binder none := declared.form | throw (IO.userError "failed uninitialized binder")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "observeFailed parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = []) "observeFailed inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "observeFailed returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = []) "observeFailed inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "observeFailed binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "observeFailed binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "observeFailed binderOrdinary"
  let ⟨binderOwner⟩ ← observed (binder.id.owner = function.typedBody.owner) "observeFailed binderOwner"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement declared.id, .statement statement.id]) "observeFailed roots"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = [.statement declared, .expression read, .statement statement]) "observeFailed nodes"
  let ⟨declaredFound⟩ ← observed (function.typedBody.lookupStatement? declared.id = some declared) "observeFailed declaredFound"
  let ⟨declaredForm⟩ ← observed (declared.form = .letDecl binder none) "observeFailed declaredForm"
  let ⟨declaredType⟩ ← observed (declared.type = .unit) "observeFailed declaredType"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "observeFailed readFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "observeFailed readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "observeFailed readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "observeFailed readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "observeFailed readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "observeFailed readCoercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "observeFailed statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.id)) "observeFailed statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "observeFailed statementType"
  return {binder, declared, read, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, binderOwner, roots, nodes, declaredFound, declaredForm, declaredType, readFound, readForm, readRaw, readType, readRequirements, readCoercions, statementFound, statementForm, statementType}

def observeIdentity (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (IdentityShape function signature) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "identity input")
  let [Node.expression read, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "identity occurrence shape")
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "observeIdentity parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.word]) "observeIdentity inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.word]) "observeIdentity returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "observeIdentity inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono .word) "observeIdentity binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "observeIdentity binderRequirements"
  let ⟨binderOrdinary⟩ ← observed (binder.comptime = false) "observeIdentity binderOrdinary"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "observeIdentity roots"
  let ⟨nodes⟩ ← observed (function.typedBody.nodes = [.expression read, .statement statement]) "observeIdentity nodes"
  let ⟨readFound⟩ ← observed (function.typedBody.lookupExpression? read.id = some read) "observeIdentity readFound"
  let ⟨readForm⟩ ← observed (read.form = .reference binder.name (.local binder.id)) "observeIdentity readForm"
  let ⟨readRaw⟩ ← observed (read.rawType = .word) "observeIdentity readRaw"
  let ⟨readType⟩ ← observed (read.type = .word) "observeIdentity readType"
  let ⟨readRequirements⟩ ← observed (read.requirements = []) "observeIdentity readRequirements"
  let ⟨readCoercions⟩ ← observed (read.coercions = []) "observeIdentity readCoercions"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "observeIdentity statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.id)) "observeIdentity statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .word) "observeIdentity statementType"
  return {binder, read, statement, parameters, inputTypes, returns, inputs, binderScheme, binderRequirements, binderOrdinary, roots, nodes, readFound, readForm, readRaw, readType, readRequirements, readCoercions, statementFound, statementForm, statementType}

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  failedFunction : CheckedFunction
  identityFunction : CheckedFunction
  failedSignature : ProgramFunctionSignature
  identitySignature : ProgramFunctionSignature
  functions : program.functions = [failedFunction, identityFunction]
  signatures : program.signatures.functions = [failedSignature, identitySignature]
  methods : program.methods = []
  failedDeclaration : failedFunction.declaration = failedSignature.id
  identityDeclaration : identityFunction.declaration = identitySignature.id
  distinct : failedSignature.id ≠ identitySignature.id
  failedShape : FailedShape failedFunction failedSignature
  identityShape : IdentityShape identityFunction identitySignature

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [failedFunction, identityFunction], [failedSignature, identitySignature] =>
      let failedShape ← observeFailed failedFunction failedSignature
      let identityShape ← observeIdentity identityFunction identitySignature
      let ⟨methods⟩ ← observed (program.methods = []) "unexpected methods"
      let ⟨failedDeclaration⟩ ← observed (failedFunction.declaration = failedSignature.id) "failed declaration"
      let ⟨identityDeclaration⟩ ← observed (identityFunction.declaration = identitySignature.id) "identity declaration"
      let ⟨distinct⟩ ← observed (failedSignature.id ≠ identitySignature.id) "distinct declarations"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl <;> rcases candidateMember with rfl | rfl
          · exact failedShape.statementTyping program.signatures
          · exact False.elim (distinct (failedDeclaration.symm.trans identity))
          · exact False.elim (distinct (identity.symm.trans identityDeclaration))
          · exact identityShape.statementTyping program.signatures
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
        failedFunction, identityFunction, failedSignature, identitySignature, functions, signatures, methods,
        failedDeclaration, identityDeclaration, distinct, failedShape, identityShape⟩
    | _, _ => throw (IO.userError "failure continuation declaration count")

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics

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
  let seeds := [SourceCompiler.Seed.declaration checked.failedSignature.id,
    SourceCompiler.Seed.declaration checked.identitySignature.id]
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
  failedRow : ObservedRow fixture fixture.failedSignature
  identityRow : ObservedRow fixture fixture.identitySignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 2
  distinctSlots : failedRow.index ≠ identityRow.index
  failedShape : FailedShape failedRow.row.function fixture.failedSignature
  identityShape : IdentityShape identityRow.row.function fixture.identitySignature
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let failedRow ← observeRow fixture fixture.failedSignature
  let identityRow ← observeRow fixture fixture.identitySignature
  let failedShape ← observeFailed failedRow.row.function fixture.failedSignature
  let identityShape ← observeIdentity identityRow.row.function fixture.identitySignature
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 2) "failure global count"
  let ⟨distinctSlots⟩ ← observed (failedRow.index ≠ identityRow.index) "failure distinct slots"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "failure local catalog"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "failure callable profile"
  return ⟨failedRow, identityRow, globalsLength, distinctSlots, failedShape, identityShape, noLocals, profile⟩

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
    ∃ (failedInput identityInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      failedInput.row = observed.failedRow.row ∧ identityInput.row = observed.identityRow.row ∧
      ∃ (failedPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued failedInput)
        (identityPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued identityInput),
      ∃ (failedHeader : ActualHeader fixture observed.failedRow.row)
        (identityHeader : ActualHeader fixture observed.identityRow.row),
        failedHeader.header = failedPacket.header ∧ identityHeader.header = identityPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons failedPacket (.cons identityPacket .nil))) := by
  obtain ⟨failedInput, failedRow, failedPacket, failedHeader, failedEq, failedSlot, failedSignature⟩ := observed.failedRow.issue
  obtain ⟨identityInput, identityRow, identityPacket, identityHeader, identityEq, identitySlot, identitySignature⟩ := observed.identityRow.issue
  refine ⟨failedInput, identityInput, failedRow, identityRow, failedPacket, identityPacket, failedHeader, identityHeader,
    failedEq, identityEq, ?_⟩
  have failedBound := (List.getElem?_eq_some_iff.mp observed.failedRow.slot.selected).1
  have identityBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  rw [observed.globalsLength] at failedBound identityBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.failedRow.index ∨ index = observed.identityRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · refine ⟨failedHeader.header, ?_, failedSlot.trans same.symm, ?_⟩
    · rw [failedEq]; exact .head _
    · rw [same, observed.failedRow.slot.selected] at found
      exact failedSignature.trans (Option.some.inj found)
  · refine ⟨identityHeader.header, ?_, identitySlot.trans same.symm, ?_⟩
    · rw [identityEq]; exact .tail _ (.head _)
    · rw [same, observed.identityRow.slot.selected] at found
      exact identitySignature.trans (Option.some.inj found)


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

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailureCertificate
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

structure ObservedCertificate (fixture : CompiledFixture) where
  certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate fixture.recipe.compiled
  accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
    fixture.source_wellFormed 64 = some certificate

def observeCertificate (fixture : CompiledFixture) : IO (ObservedCertificate fixture) := do
  match accepted : CallableIndexedOwnedPreparedProgramAdmission.certify fixture.recipe.compiled
      fixture.source_wellFormed 64 with
  | none => throw (IO.userError "original lexical program certificate rejected")
  | some certificate => return ⟨certificate, accepted⟩

def probeCertificate : IO Unit := do
  let fixture ← compiledFixture
  let _certificate ← observeCertificate fixture
  IO.println "CERTIFIED_LEXICAL_PROGRAM_PASS: original checker1000/compiler100; complete certificate64"

end Tests.SourceCoreCertifiedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureFacts
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
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

theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.failedRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.identityRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 2 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have makeBound := (List.getElem?_eq_some_iff.mp observed.failedRow.slot.selected).1
  have readBound := (List.getElem?_eq_some_iff.mp observed.identityRow.slot.selected).1
  rw [observed.globalsLength] at makeBound readBound
  have casesIndex : index = observed.failedRow.index ∨ index = observed.identityRow.index := by
    have distinct := observed.distinctSlots
    omega
  rcases casesIndex with same | same
  · left
    have actualIndex := (observed.failedRow.prepared_slot failedHeader.prepared).2
    rw [same, ← actualIndex, failedHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) failedHeader.prepared.same
  · right
    have actualIndex := (observed.identityRow.prepared_slot identityHeader.prepared).2
    rw [same, ← actualIndex, identityHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) identityHeader.prepared.same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member


theorem ActualHeader.failed_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.failedRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.failedShape.returns]
  rfl

theorem ObservedProgram.failed_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.failedRow.row.function.typedBody id node →
      ∀ parameters result body, node.form = .lambda parameters result body → False := by
  intro id node found parameters result body form
  have member := found.1
  rw [observed.failedShape.nodes] at member
  have same : node = observed.failedShape.read := by simpa using member
  subst node
  rw [observed.failedShape.readForm] at form
  cases form

theorem ObservedProgram.failed_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.failedRow.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  have member := (lookupExpression?_sound found).1
  rw [observed.failedShape.nodes] at member
  have same : node = observed.failedShape.read := by simpa using member
  subst node
  exact .inl ⟨_, _, observed.failedShape.readForm, observed.failedShape.readRequirements,
    observed.failedShape.readCoercions⟩

theorem ActualHeader.identity_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  have result := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).2
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same, result,
    observed.identityShape.returns]
  rfl

theorem ObservedProgram.identity_no_lambda {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∀ id node, ContainsExpression observed.identityRow.row.function.typedBody id node →
      ∀ parameters result body, node.form = .lambda parameters result body → False := by
  intro id node found parameters result body form
  have member := found.1
  rw [observed.identityShape.nodes] at member
  have same : node = observed.identityShape.read := by simpa using member
  subst node
  rw [observed.identityShape.readForm] at form
  cases form

theorem ObservedProgram.identity_metadata {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named observed.identityRow.row.function.typedBody := by
  apply CallableIndexedOwnedPreparedStagedReadLambdaMetadata.metadata _ named _ observed.noLocals
  intro id node found
  have member := (lookupExpression?_sound found).1
  rw [observed.identityShape.nodes] at member
  have same : node = observed.identityShape.read := by simpa using member
  subst node
  exact .inl ⟨_, _, observed.identityShape.readForm, observed.identityShape.readRequirements,
    observed.identityShape.readCoercions⟩

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply False.elim
    have found := code.sourceFound
    rcases observed.cached_source failedHeader identityHeader support.caller.selected with original | original
    · rw [support.source.trans original] at found
      exact False.elim (observed.failed_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    · rw [support.source.trans original] at found
      exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureBodies
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem ActualHeader.failed_statements {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.function.body = [observed.failedShape.declared.id, observed.failedShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.failedShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem ActualHeader.failed_lexical_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.failed_statements]
  exact .absent observed.failedShape.declaredFound observed.failedShape.declaredForm
    (.returnValue [] observed.failedShape.statementFound observed.failedShape.statementForm)

theorem ActualHeader.identity_statements {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.body = [observed.identityShape.statement.id] := by
  rw [actual.aligned.function]
  change actual.prepared.compilation.statements = _
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.identityShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem ActualHeader.identity_lexical_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.identity_statements]
  exact .returnValue [] observed.identityShape.statementFound observed.identityShape.statementForm

def ActualHeader.lexical_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .lexical receipt }

theorem ObservedProgram.failed_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.failedRow.row.function.typedBody observed.failedShape.binder.id =
      .ok observed.failedShape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.failedShape.inputs,
    observed.failedShape.nodes, observed.failedShape.declaredForm, observed.failedShape.readForm,
    observed.failedShape.statementForm, observed.failedShape.binderOwner, observed.failedShape.binderScheme,
    TypeSystem.Scheme.mono, observed.failedShape.binderRequirements]

theorem ActualHeader.failed_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => id = observed.failedShape.read.id)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  rw [source, observed.failedShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, actual.failed_statements]
  have unique : NodeOccurrencesUnique observed.failedRow.row.function.typedBody := source ▸ actual.header.unique
  cases typed with
  | cons head tail =>
    cases tail with
    | singleton last =>
      cases head with
      | letUninitialized contains form mono generalized extended type =>
        have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.declaredFound)
        cases same
        rw [observed.failedShape.declaredForm] at form
        cases (StatementForm.letDecl.inj form).1
        apply GenericLexicalStatements.Syntax.uninitialized observed.failedShape.declaredFound observed.failedShape.declaredForm
          observed.failed_local_declaration mono extended (by rw [observed.failedShape.inputs]; rfl)
        cases last with
        | returnValue contains form expression type =>
          have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.statementFound)
          cases same
          rw [observed.failedShape.statementForm] at form
          cases Option.some.inj (StatementForm.returnStmt.inj form)
          exact .returnValue [] observed.failedShape.statementFound observed.failedShape.statementForm type
            observed.failedShape.readFound (observed.failedShape.readType.trans actual.failed_result_type.symm)
            (by simpa only [observed.failedShape.readType, actual.failed_result_type] using expression) rfl
        | _ =>
          have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.statementFound)
          cases same
          simp_all [observed.failedShape.statementForm]
      | _ =>
        have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.declaredFound)
        cases same
        simp_all [observed.failedShape.declaredForm]

theorem ActualHeader.identity_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => id = observed.identityShape.read.id)
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  have source := actual.source
  rw [source, observed.identityShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [source, actual.identity_statements]
  have unique : NodeOccurrencesUnique observed.identityRow.row.function.typedBody := source ▸ actual.header.unique
  cases typed with
  | singleton last =>
    cases last with
    | returnValue contains form expression type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.identityShape.statementFound)
      cases same
      rw [observed.identityShape.statementForm] at form
      cases Option.some.inj (StatementForm.returnStmt.inj form)
      exact .returnValue [] observed.identityShape.statementFound observed.identityShape.statementForm type
        observed.identityShape.readFound (observed.identityShape.readType.trans actual.identity_result_type.symm)
        (by simpa only [observed.identityShape.readType, actual.identity_result_type] using expression) rfl
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.identityShape.statementFound)
      cases same
      simp_all [observed.identityShape.statementForm]

theorem ActualHeader.failed_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.failedRow.entryMember receipt _ actual.failed_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  subst id
  have same : node = observed.failedShape.read :=
    Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.failedShape.readFound))
  subst node
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.failed_metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    observed.failedShape.readForm
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

theorem ActualHeader.identity_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt actual.header)
    (headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)))
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) headers)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedLexicalSupport.Support headers
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  apply Nonempty.intro
  apply CallableIndexedOwnedPreparedNamedLexicalCollectors.of_compiler actual.prepared actual.aligned
    fixture.recipePrepared fixture.source_wellFormed complete (bootstrap_zero fixture.recipe.compiled)
    observed.identityRow.entryMember receipt _ actual.identity_syntax
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType _native
  subst id
  have same : node = observed.identityShape.read :=
    Option.some.inj (found.symm.trans (by rw [actual.source]; exact observed.identityShape.readFound))
  subst node
  obtain ⟨root⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.of_accepted
    actual.prepared actual.aligned actual.diagnostic receiver fixture.source_wellFormed
    (by rw [actual.source]; exact observed.identity_metadata actual.prepared.named)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected)
    ((RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).evidence selected) fields
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact declarations)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact found)
    observed.identityShape.readForm
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact typed)
    (by rw [(RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected]; exact accepted)
  exact .recursive root

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureHeap
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem local_fault {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {failure : Staging.Recursive.Failure} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location {type := .word, value := none})
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment before id (.fault failure) after) :
    failure = .semantic (.uninitializedLocation location) ∧ after = before := by
  have same {other : ExpressionNode} (contains : ContainsExpression scope.source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | generalizedLocal contains otherForm _ actualLookup actualRead descriptor _ _ _
  | generalizedLocalRequirement contains otherForm _ actualLookup actualRead descriptor _ _ _ =>
    have nodeEq := same contains
    cases nodeEq
    rw [form] at otherForm
    cases otherForm
    have sameLocation := actualLookup.functional lookup
    subst_vars
    have sameCell := actualRead.functional read
    cases sameCell
    cases descriptor
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | atomicFault contains atomic uncoerced raw =>
    have nodeEq := same contains
    cases nodeEq
    rw [form] at raw
    cases raw with
    | localUnbound _ missing => exact False.elim (missing.excludes_lookup lookup)
    | localDangling _ actual dangling =>
      have eq := actual.functional lookup
      subst_vars
      exact False.elim (dangling.excludes_read read)
    | localUninitialized _ actual _ _ _ _ =>
      have eq := actual.functional lookup
      subst_vars
      exact ⟨rfl, rfl⟩
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryRightFault occurrence _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ =>
    obtain ⟨other, contains, otherForm, _requirements, _coercions⟩ := occurrence
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem return_fault {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    {failure : Staging.Recursive.Failure} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment before
      (id :: rest) finalContext (.fault failure) after) :
    ∃ childSize, Staging.Recursive.Size.Expression program registry childSize scope context environment before
      expression (.fault failure) after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | returnFault contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact ⟨_, child⟩
  | forInitializerFault contains otherForm _ | forFault contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchFault contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockFault contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileFault contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifConditionFault contains otherForm _ | ifFault contains otherForm _ _
  | ifFallthrough contains otherForm _ _ _
  | expressionFault contains otherForm _ | letFault contains otherForm _ _
  | discard contains otherForm _ _ | letUninitialized contains otherForm _ _ _ _
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | assignProjectedRootFault contains otherForm _ _
  | assignProjectedKeysFault contains otherForm _ _ _
  | assignProjectedGetterFault contains otherForm _ _ _
  | assignProjectedRhsFault contains otherForm _ _ _ _
  | assignProjectedWriteFault contains otherForm _ _ _ _ _
  | bitNotProjected contains otherForm _ _ _ _ _
  | bitNotProjectedRootFault contains otherForm _ _
  | bitNotProjectedKeysFault contains otherForm _ _ _
  | bitNotProjectedGetterFault contains otherForm _ _ _
  | bitNotBare contains otherForm _ _ _ | bitNotBareFault contains otherForm _ _
  | assignBareOperands contains otherForm _ _ _ _ _ _ _ | assignBareFault contains otherForm _ _
  | assignBareUnbound contains otherForm _ _ | assignBareDangling contains otherForm _ _ _
  | letGeneralized contains otherForm _ _ _ _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

/-- The first failed Source call allocates the absent cell before reading it;
its returned heap is exactly that allocation's heap. -/
theorem ActualHeader.failed_heap
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      size invocation context before (.global global) [] (.fault failure) after) :
    ∃ location, failure = .semantic (.uninitializedLocation location) ∧
      Dynamic.Heap.Allocates before .word none location after ∧
      Dynamic.Heap.Reads after location {type := .word, value := none} := by
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  obtain ⟨sourceFinal, sourceFacts, sourceTyped, _complete⟩ :=
    RecursiveNamedHeaderSourceTyping.statements actual.header fixture.source_wellFormed
  rw [← sourceEq] at sourceTyped
  have faultOutcome := Staging.Recursive.TypedControlBoundary.body_fault
    (Staging.Recursive.TypedControlBoundary.function unique sourceTyped rfl body.sound) converted
  subst bodyOutcome
  rw [parameters] at parametersAllocated
  cases parametersAllocated
  rw [actual.failed_statements] at body
  have declaredFound : child.source.lookupStatement? observed.failedShape.declared.id = some observed.failedShape.declared := by
    rw [sourceEq, actual.source]; exact observed.failedShape.declaredFound
  have same {other : StatementNode} (contains : ContainsStatement child.source observed.failedShape.declared.id other) :
      other = observed.failedShape.declared :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans declaredFound)
  cases body with
  | forInitializerFault contains otherForm _ | forFault contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchFault contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockFault contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileFault contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifConditionFault contains otherForm _ | ifFault contains otherForm _ _
  | ifFallthrough contains otherForm _ _ _
  | returnFault contains otherForm _ | expressionFault contains otherForm _
  | letFault contains otherForm _ _ | discard contains otherForm _ _
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | assignProjectedRootFault contains otherForm _ _
  | assignProjectedKeysFault contains otherForm _ _ _
  | assignProjectedGetterFault contains otherForm _ _ _
  | assignProjectedRhsFault contains otherForm _ _ _ _
  | assignProjectedWriteFault contains otherForm _ _ _ _ _
  | bitNotProjected contains otherForm _ _ _ _ _
  | bitNotProjectedRootFault contains otherForm _ _
  | bitNotProjectedKeysFault contains otherForm _ _ _
  | bitNotProjectedGetterFault contains otherForm _ _ _
  | bitNotBare contains otherForm _ _ _ | bitNotBareFault contains otherForm _ _
  | assignBareOperands contains otherForm _ _ _ _ _ _ _ | assignBareFault contains otherForm _ _
  | assignBareUnbound contains otherForm _ _ | assignBareDangling contains otherForm _ _ _
  | letGeneralized contains otherForm _ _ _ _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [observed.failedShape.declaredForm] at impossible
    cases impossible
  | letUninitialized contains form _mono _extended allocated next =>
    rename_i location
    have nodeEq := same contains
    cases nodeEq
    rw [observed.failedShape.declaredForm] at form
    cases form
    obtain ⟨childSize, expression⟩ := return_fault unique
      (by rw [sourceEq, actual.source]; exact observed.failedShape.statementFound)
      observed.failedShape.statementForm next
    have cell := allocated.reads_new
    simp only [observed.failedShape.binderScheme, TypeSystem.Scheme.mono] at cell
    obtain ⟨failureEq, heapEq⟩ := local_fault unique
      (by rw [sourceEq, actual.source]; exact observed.failedShape.readFound)
      observed.failedShape.readForm observed.failedShape.readCoercions .head cell expression
    subst after
    refine ⟨location, failureEq, ?_, cell⟩
    simpa only [observed.failedShape.binderScheme, TypeSystem.Scheme.mono] using allocated

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

/-- The following identity call only allocates its actual Word parameter.
Any earlier cell therefore remains present with its original contents. -/
theorem ActualHeader.identity_heap
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      size invocation context before (.global global) [.word word] (.value (.word word)) after) :
    ∃ location, Dynamic.Heap.Allocates before .word (some (.word word)) location after := by
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  rw [actual.identity_result_type] at converted
  cases converted
  rw [parameters] at parametersAllocated
  cases parametersAllocated with
  | cons allocated remaining =>
    cases remaining
    have cell := allocated.reads_new
    simp only [observed.identityShape.binderScheme, TypeSystem.Scheme.mono] at cell
    rw [actual.identity_statements] at body
    have expression := returned_expression unique
      (by rw [sourceEq, actual.source]; exact observed.identityShape.statementFound)
      observed.identityShape.statementForm body
    obtain ⟨_word, sameHeap⟩ := initialized_read unique
      (by rw [sourceEq, actual.source]; exact observed.identityShape.readFound)
      observed.identityShape.readForm observed.identityShape.readCoercions .head cell expression
    subst after
    exact ⟨_, by simpa only [observed.identityShape.binderScheme, TypeSystem.Scheme.mono] using allocated⟩

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureRuntime
/-! Actual initial failure, returned session and subsequent successful call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

def seed : Core.Word := Core.Word.ofNatModulo 37

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- The first failed call retains the actual session after local allocation. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.failedRow.row.key [] runOptions.inputValidationFuel = .ok checkpoint
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt observed.failedRow.row.key [] runOptions (.ok (.failed reason returned))

def observePublicRun (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.failedRow.row.key [] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.failedRow.row.key [] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed reason returned) =>
        return ⟨opened.val, opened.property, fresh.val, fresh.property, session, ready,
          checkpoint, started, reason, returned, result ▸ executed.property⟩
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "failure public run exhausted")
      | .ok (.succeeded _) => throw (IO.userError "uninitialized read unexpectedly succeeded")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed
  executed : fixture.recipe.compiled.indexed.runSource observed.failedRow.row.key []
    runOptions.executionFuel runOptions.inputValidationFuel = .ok completion

def observeReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedReceiver fixture observed) := do
  match executed : fixture.recipe.compiled.indexed.runSource observed.failedRow.row.key []
      runOptions.executionFuel runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok completion => return ⟨completion, executed⟩


private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedPublicRun.start_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
      RecursiveNamedPublicStartMeaning.StartAt session observed.failedRow.row.key [] runOptions.inputValidationFuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩


theorem ObservedPublicRun.metadata_at_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedPublicRun fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.failedRow.row.key [] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  cases member


structure ObservedContinuation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed) where
  checkpoint : SourceCoreExecution.Checkpoint first.artifact
  started : first.returned.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion first.artifact
  executed : first.returned.RunAt observed.identityRow.row.key [.word seed] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observeContinuation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed) : IO (ObservedContinuation first) := do
  match started : first.returned.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← first.returned.runWithReceipt observed.identityRow.row.key [.word seed] runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "identity failed after initial failure")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "identity exhausted")
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word seed then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "identity did not return 37")

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureSupports
/-! Both authentic issuer packets produce complete static lexical support.
The Type-valued body dispatcher uses their actual physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

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
  failedInput : Input fixture.recipe.compiled
  identityInput : Input fixture.recipe.compiled
  failedRow : failedInput.row = observed.failedRow.row
  identityRow : identityInput.row = observed.identityRow.row
  failedPacket : Issued failedInput
  identityPacket : Issued identityInput
  failedHeader : ActualHeader fixture observed.failedRow.row
  identityHeader : ActualHeader fixture observed.identityRow.row
  failedEq : failedHeader.header = failedPacket.header
  identityEq : identityHeader.header = identityPacket.header
  rows : Inventory [failedInput, identityInput]
  rowsEq : rows = .cons failedPacket (.cons identityPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([failedInput, identityInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : failedHeader.header.slot ≠ identityHeader.header.slot
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
  failedDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named failedHeader.header.named.signature.key)
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨failedInput, identityInput, failedRow, identityRow, failedPacket, identityPacket,
    failedHeader, identityHeader, failedEq, identityEq, complete⟩ := observed.inventory
  let rows : Inventory [failedInput, identityInput] := .cons failedPacket (.cons identityPacket .nil)
  have headerList : headers rows = [failedHeader.header, identityHeader.header] := by
    simp only [rows, headers, failedEq, identityEq]
  have failedIndex : failedHeader.header.slot = observed.failedRow.index :=
    failedHeader.aligned.slot.trans (observed.failedRow.prepared_slot failedHeader.prepared).2
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have slotsDistinct : failedHeader.header.slot ≠ identityHeader.header.slot := by
    rw [failedIndex, identityIndex]
    exact observed.distinctSlots
  have inputDistinct : failedInput.prepared.index ≠ identityInput.prepared.index := by
    have left : failedHeader.header.slot = failedInput.prepared.index := by
      rw [failedEq]; exact failedPacket.aligned.slot
    have right : identityHeader.header.slot = identityInput.prepared.index := by
      rw [identityEq]; exact identityPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  obtain ⟨failedReceipt⟩ := failedHeader.failed_lexical_receipt
  obtain ⟨identityReceipt⟩ := identityHeader.identity_lexical_receipt
  let failedBody := failedHeader.lexical_body failedReceipt
  let identityBody := identityHeader.lexical_body identityReceipt
  obtain ⟨failedSupport⟩ := failedHeader.failed_support failedReceipt (headers rows) complete (registry := registry) receiver
  obtain ⟨identitySupport⟩ := identityHeader.identity_support identityReceipt (headers rows) complete (registry := registry) receiver
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo slotsDistinct property
      ⟨failedBody, failedSupport⟩ ⟨identityBody, identitySupport⟩ header (headerList ▸ member)
  exact ⟨{
    failedInput := failedInput
    identityInput := identityInput
    failedRow := failedRow
    identityRow := identityRow
    failedPacket := failedPacket
    identityPacket := identityPacket
    failedHeader := failedHeader
    identityHeader := identityHeader
    failedEq := failedEq
    identityEq := identityEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family failedHeader identityHeader (actualStagePrepared fixture) association
    failedDescriptor := failedHeader.descriptor failedStages
    identityDescriptor := identityHeader.descriptor identityStages }⟩

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureRuntime
/-! Actual initial failure, returned session and subsequent successful call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

def seed : Core.Word := Core.Word.ofNatModulo 37

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- The first failed call retains the actual session after local allocation. -/
structure ObservedPublicRun (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.failedRow.row.key [] runOptions.inputValidationFuel = .ok checkpoint
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.RunAt observed.failedRow.row.key [] runOptions (.ok (.failed reason returned))

def observePublicRun (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.failedRow.row.key [] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.failedRow.row.key [] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed reason returned) =>
        return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
          checkpoint, started, reason, returned, result ▸ executed.property⟩
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "failure public run exhausted")
      | .ok (.succeeded _) => throw (IO.userError "uninitialized read unexpectedly succeeded")

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.failedRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

theorem ObservedPublicRun.start_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
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
      RecursiveNamedPublicStartMeaning.StartAt session observed.failedRow.row.key [] runOptions.inputValidationFuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, _program, sessionAt, checkpointAt, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted executed.opened executed.started
  have same := recipe_unique opened.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    opened, prepared, sessionAt, checkpointAt, started⟩


theorem ObservedPublicRun.metadata_at_start {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (executed : ObservedPublicRun fixture observed)
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {world : Core.StoreTyping} {store : Core.Store} {native : Core.Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (opened : executed.artifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact)
    (sessionAt : executed.session.IndexedAt session)
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.failedRow.row.key [] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  apply started.simple_registry (booted.registry_at initial)
  intro value member
  cases member


end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureCommon
/-! Concrete receiving diagnostics and retained state for the actual public
sequence. These records are constructed by public execution proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

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
    support.failedHeader.header session mapping world heap store caller entries

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
      support.failedHeader.header.function.context before (.global function) arguments outcome after

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreInitialLexicalFailureSelection
/-! The original first-match receipts select the exact member of the two-row
inventory. Raw types come from checked Source signatures and the accepted
specialization, independently of execution or native type tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedProgram.keys_distinct {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) : observed.failedRow.row.key ≠ observed.identityRow.row.key := by
  intro same
  have globals : observed.failedRow.global.key = observed.identityRow.global.key :=
    observed.failedRow.globalKey.trans (same.trans observed.identityRow.globalKey.symm)
  exact observed.distinctSlots (observed.failedRow.slot.unique observed.identityRow.slot globals).2

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

theorem selected_failed_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [failedHeader.header, identityHeader.header] root header)
    (key : root.key = observed.failedRow.row.key) : header = failedHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · exact same
  · have same := List.mem_singleton.mp rest
    have headerKey := (selected_key selected).trans key
    rw [same, identityHeader.key] at headerKey
    exact False.elim (observed.keys_distinct headerKey.symm)

theorem selected_identity_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (failedHeader : ActualHeader fixture observed.failedRow.row)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [failedHeader.header, identityHeader.header] root header)
    (key : root.key = observed.identityRow.row.key) : header = identityHeader.header := by
  rcases List.mem_cons.mp selected.member with same | rest
  · have headerKey := (selected_key selected).trans key
    rw [same, failedHeader.key] at headerKey
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
  (failedHeader : ActualHeader fixture observed.failedRow.row)
  (identityHeader : ActualHeader fixture observed.identityRow.row)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {session : SourceCoreIndexedSession.Session nativeArtifact}
  {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
  {world : Core.StoreTyping} {store : Core.Store}

theorem selected_failed (request : Started [failedHeader.header, identityHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.failedRow.row.key arguments fuel world store) :
    request.header = failedHeader.header :=
  selected_failed_root failedHeader identityHeader request.selected (started_key request)

theorem selected_identity (request : Started [failedHeader.header, identityHeader.header]
    fixture.recipePrepared publicCheckpoint session observed.identityRow.row.key arguments fuel world store) :
    request.header = identityHeader.header :=
  selected_identity_root failedHeader identityHeader request.selected (started_key request)

theorem selected_failed_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [failedHeader.header, identityHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.failedRow.row.key arguments fuel world store) : request.header = failedHeader.header := by
  subst headers
  exact selected_failed failedHeader identityHeader request

theorem selected_identity_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [failedHeader.header, identityHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.identityRow.row.key arguments fuel world store) : request.header = identityHeader.header := by
  subst headers
  exact selected_identity failedHeader identityHeader request
end StartedSelection

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    CallableIndexedOwnedPreparedFiniteNamedInventories.headers support.rows =
      [support.failedHeader.header, support.identityHeader.header] := by
  rw [support.rowsEq]
  simp only [CallableIndexedOwnedPreparedFiniteNamedInventories.headers, support.failedEq, support.identityEq]




theorem ActualHeader.failed_inputs {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [] := by
  have raw := (observed.failedRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .head _) actual).1
  rw [observed.failedShape.inputTypes] at raw
  rw [← actual.source, actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.failed_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.failed_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.identity_inputs {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word] := by
  have raw := (observed.identityRow.source_types
    (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)) actual).1
  rw [observed.identityShape.inputTypes] at raw
  rw [← actual.source, actual.header.inputs] at raw
  simpa only [List.map_map, Function.comp_def] using raw

theorem ActualHeader.identity_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.identity_result_type] at projected
  exact (Except.ok.inj projected).symm

end Tests.SourceCoreInitialLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailureHeaders
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}

theorem eligible_row (row : ObservedRow fixture signature) :
    ∃ selected : CertifiedPublicSession.EligibleRow fixture.recipe.compiled row.row.key,
      selected.named.specialized = row.row := by
  obtain ⟨prepared⟩ := fixture.prepared row.member
  obtain ⟨signatureEq, indexEq⟩ := row.prepared_slot prepared
  have eligible : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Eligible fixture.recipe.compiled
      prepared.named.specialized := by
    rw [prepared.same]
    refine ⟨prepared.origin, ?_, row.ordinary, row.inputsOrdinary⟩
    simp only [row.parameters, ParameterSubstitution.RangeWellFormed, List.not_mem_nil,
      false_implies, implies_true]
  exact ⟨⟨prepared.named, prepared.index, row.global, prepared.selected,
    by rw [indexEq]; exact row.slot, row.globalKey, eligible⟩, prepared.same⟩

theorem header_of_member (row : ObservedRow fixture signature)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (member : header ∈ headers rows) (source : header.named.specialized = row.row) :
    ∃ actual : ActualHeader fixture row.row, actual.header = header := by
  obtain ⟨input, packet, _retained, sameHeader⟩ := rows.mem_headers header member
  subst header
  have sameRow : input.row = row.row := input.prepared.same.symm.trans
    ((congrArg (·.specialized) packet.aligned.named.symm).trans source)
  have parameters : input.row.parameterSubstitution = [] := sameRow ▸ row.parameters
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row =
      CallableNamedMetadata.instantiation input.row := by
    simp [CallableNamedCanonicalOrder.retainedInstantiation, CallableNamedMetadata.instantiation, parameters]
  let actual : ActualHeader fixture input.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
    header := packet.header
    aligned := by simpa only [metadata] using packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  have transported : ∀ (left right : SourceSpecialization.SpecializedFunction)
      (same : left = right) (value : ActualHeader fixture left),
      (same ▸ value : ActualHeader fixture right).header = value.header := by
    intro left right same value
    cases same
    rfl
  exact ⟨sameRow ▸ actual, transported _ _ sameRow actual⟩

theorem header_types
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)) :
    header.types = header.bindings.map (fun binding => binding.1.scheme.body) := by
  have same := Dynamic.MonoBindersExtend.bodyTypes_eq header.extended
  rw [header.parameters] at same
  simpa only [List.map_map, Function.comp_def] using same.symm

end Tests.SourceCoreCertifiedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailureRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

abbrev First (fixture : CompiledFixture) (observed : ObservedProgram fixture) :=
  Tests.SourceCoreDirectFailure.ObservedPublicRun fixture observed

def first_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : RecursiveNamedPublicPhysicalSessionState.StartedCall
      first.session observed.failedRow.row.key [] runOptions := ⟨first.checkpoint, first.started⟩

def original_first {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : ObservedPublicRun fixture observed := {
  artifact := first.artifact, opened := first.opened, bootstrap := first.bootstrap,
  fresh := first.fresh, session := first.session, ready := first.ready,
  checkpoint := first.checkpoint, started := first.started, reason := first.reason,
  returned := first.returned, executed := first.executed }

def continuation_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {first : First fixture observed} (next : ObservedContinuation (original_first first)) :
    RecursiveNamedPublicPhysicalSessionState.Call first.returned observed.identityRow.row.key [.word seed] runOptions :=
  ⟨⟨next.checkpoint, next.started⟩, next.completion, next.executed⟩

theorem first_returned_ready {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : First fixture observed) : first.returned.ExportsReady := by
  obtain ⟨_artifact, _session, checkpoint, _root, _world, _store, _native, _values,
      _opened, _prepared, atSession, atCheckpoint, started⟩ := first.start_receipt
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := first.executed
  have same : publicCheckpoint = first.checkpoint := Except.ok.inj (accepted.symm.trans first.started)
  subst publicCheckpoint
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (started.original.initial_registry.exportsReady (atSession.exportsReady_iff.mp ready)))

structure FreshIdentity (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.Call session observed.identityRow.row.key [.word seed] runOptions
  returned : call.completion.value = .word seed

def observeFreshIdentity (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (FreshIdentity fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "original identity bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.identityRow.row.key [.word seed] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.identityRow.row.key [.word seed] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "original fresh identity failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "original fresh identity exhausted")
      | .ok (.succeeded completion) =>
        if returned : completion.value = .word seed then
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            ⟨⟨checkpoint, started⟩, completion, result ▸ executed.property⟩, returned⟩
        else throw (IO.userError "original fresh identity did not return37")

end Tests.SourceCoreCertifiedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailureMeaning
/-! The unchanged lexical program uses one automatically issued physical
session after its first failure, then continues with identity(37). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CertifiedPublicSession (Issued Initial)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) where
  initial : Initial issued (first_call first)
  actual : ActualHeader fixture observed.failedRow.row
  headerEq : initial.header = actual.header
  after : issued.State initial.header first.returned []
  location : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word none location after.heap
  absent : Dynamic.Heap.Reads after.heap location {type := .word, value := none}
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
    (.fault (.semantic (.uninitializedLocation location))) after.heap
  decoded : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
    (.semantic (.uninitializedLocation location)) first.reason
  forward : RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.semantic (.uninitializedLocation location)) (first_call first) after.heap

structure ContinuationMeaning {issued : Issued fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    next.checkpoint before.after.session observed.identityRow.row.key [.word seed]
    runOptions.inputValidationFuel before.after.world before.after.store
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : request.header = actual.header
  after : issued.State before.initial.header next.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates before.after.heap .word (some (.word seed)) parameter after.heap
  absent : Dynamic.Heap.Reads after.heap before.location {type := .word, value := none}
  trace : SourceCall before.initial.header request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
    (.value (.word seed)) after.heap
  forward : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows before.initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) (continuation_call next).toStartedCall after.heap

structure FreshMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) where
  initial : Initial issued fresh.call.toStartedCall
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : initial.header = actual.header
  after : issued.State initial.header fresh.call.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word (some (.word seed)) parameter after.heap
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
    (.value (.word seed)) after.heap
  forward : RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) fresh.call.toStartedCall after.heap

theorem first_meaning (admission : ObservedCertificate fixture)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.failedRow
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued admission.certificate fixture.source_wellFormed first.opened
    (first_call first) first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.failedRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [] initial.header.types := by
    rw [header_types, ← actualEq, actual.failed_inputs]
    exact .nil
  have simple : ∀ value ∈ ([] : List SourceCorePublicValues.Value), SourceCoreIndexedSession.SimplePublic value := by
    intro value member; cases member
  obtain ⟨failure, after, trace, decoded⟩ := initial.reflect_failure first.returned first.reason first.executed
    simple inputTypes .nil (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨location, failureEq, allocated, absent⟩ := actual.failed_heap
    (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
      (.fault (.semantic (.uninitializedLocation location))) after.heap :=
    ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, location, allocated, absent,
    sourceCall, failureEq ▸ decoded, initial.forward_failure simple inputTypes .nil sourceCall⟩⟩⟩

theorem continuation_meaning {issued : Issued fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) :
    Nonempty (ContinuationMeaning before stages next) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before.after (continuation_call next).toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [← actualEq, actual.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have raw : request.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : request.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := issued.reflect_scalar before.after (.word seed) (continuation_call next)
    next.returned request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall before.initial.header request.header
      (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  have ready : first.returned.ExportsReady := first_returned_ready first
  exact ⟨⟨request, actual, actualEq.symm, after, parameter, allocated,
    allocated.preserves_read before.absent, sourceCall,
    issued.forward_scalar before.after (.word seed) (continuation_call next).toStartedCall request
      inputs raw native ready sourceCall⟩⟩

theorem fresh_meaning (admission : ObservedCertificate fixture)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (FreshMeaning issued stages fresh) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued admission.certificate fixture.source_wellFormed fresh.opened
    fresh.call.toStartedCall fresh.bootstrap fresh.fresh fresh.authority
    (show fresh.bootstrap.ReadyAt 100000 fresh.session from .single fresh.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [header_types, ← actualEq, actual.identity_inputs]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have simple : ∀ value ∈ [.word seed], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact .word seed
  have raw : initial.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : initial.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := initial.reflect_scalar (.word seed) fresh.returned simple inputTypes inputMeanings
    raw native (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, parameter, allocated, sourceCall,
    initial.forward_scalar (.word seed) simple inputTypes inputMeanings raw native sourceCall⟩⟩⟩

end Tests.SourceCoreCertifiedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailurePublicExecution
/-! The original lexical failure and identity declarations now consume the
whole-program certificate and automatic catalog for their public conclusions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCertifiedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

/-- Actual failure, continuation and fresh scalar success retain their original
Source heaps, with sufficient-fuel conclusions at each actual checkpoint. -/
theorem closed_outcomes (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedCertificate fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (first : First fixture observed)
    (next : ObservedContinuation (original_first first))
    (fresh : FreshIdentity fixture observed) :
    ∃ issued : CertifiedPublicSession.Issued fixture.recipe,
      ∃ before : FirstMeaning issued failedStages first,
        Nonempty (ContinuationMeaning before identityStages next) ∧
        ∃ freshIssued : CertifiedPublicSession.Issued fixture.recipe,
          Nonempty (FreshMeaning freshIssued identityStages fresh) := by
  obtain ⟨issued, ⟨before⟩⟩ := first_meaning admission failedStages first
  exact ⟨issued, before, continuation_meaning before identityStages next,
    fresh_meaning admission identityStages fresh⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeCertificate fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let first ← Tests.SourceCoreDirectFailure.observePublicRun fixture observed
  let next ← observeContinuation (original_first first)
  let fresh ← observeFreshIdentity fixture observed
  have _meaning := closed_outcomes fixture observed admission failedStages identityStages first next fresh
  IO.println "CERTIFIED_SESSION_OUTCOMES_PASS: original checker1000/compiler100; first uninitialized fault retains absent cell; same session identity(37) preserves it; fresh identity(37); automatic catalog, empty handle histories and all three forward bounds"

end Tests.SourceCoreCertifiedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreCertifiedLexicalFailureSourceOutcomes
/-! The original failed call and both identity calls have independent Dynamic
outcomes at the exact heaps returned by the authentic public reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCertifiedLexicalFailure.SourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CertifiedPublicSession (Issued)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}

theorem first_fault {stages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} (meaning : FirstMeaning issued stages first) :
    PlainFault meaning.initial.header meaning.initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.initial.header.function)
      ⟨[]⟩ [] (.uninitializedLocation meaning.location) meaning.after.heap :=
  meaning.trace.semanticFault_plain

theorem continuation_value {failedStages : ObservedStages fixture observed.failedRow}
    {first : First fixture observed} {before : FirstMeaning issued failedStages first}
    {stages : ObservedStages fixture observed.identityRow}
    {next : ObservedContinuation (original_first first)}
    (meaning : ContinuationMeaning before stages next) :
    PlainValue before.initial.header meaning.request.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.request.header.function)
      before.after.heap [.word seed] (.word seed) meaning.after.heap := meaning.trace.value_plain

theorem fresh_value {stages : ObservedStages fixture observed.identityRow}
    {fresh : FreshIdentity fixture observed} (meaning : FreshMeaning issued stages fresh) :
    PlainValue meaning.initial.header meaning.initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] meaning.initial.header.function)
      ⟨[]⟩ [.word seed] (.word seed) meaning.after.heap := meaning.trace.value_plain

/-- The same witnesses retain the absent cell, its survival after continuation,
empty handle histories, actual diagnostics and all three forward fuel bounds. -/
theorem closed_outcomes (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedCertificate fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (first : First fixture observed)
    (next : ObservedContinuation (original_first first))
    (fresh : FreshIdentity fixture observed) :
    ∃ (issued : Issued fixture.recipe) (before : FirstMeaning issued failedStages first)
      (after : ContinuationMeaning before identityStages next)
      (freshIssued : Issued fixture.recipe) (freshMeaning : FreshMeaning freshIssued identityStages fresh),
      PlainFault before.initial.header before.initial.header
        (RecursiveStageRegistry.scope failedStages.sidecar [] before.initial.header.function)
        ⟨[]⟩ [] (.uninitializedLocation before.location) before.after.heap ∧
      PlainValue before.initial.header after.request.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] after.request.header.function)
        before.after.heap [.word seed] (.word seed) after.after.heap ∧
      PlainValue freshMeaning.initial.header freshMeaning.initial.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] freshMeaning.initial.header.function)
        ⟨[]⟩ [.word seed] (.word seed) freshMeaning.after.heap := by
  obtain ⟨issued, before, ⟨after⟩, freshIssued, ⟨freshMeaning⟩⟩ :=
    SourceCoreCertifiedLexicalFailure.closed_outcomes fixture observed admission failedStages identityStages first next fresh
  exact ⟨issued, before, after, freshIssued, freshMeaning,
    first_fault before, continuation_value after, fresh_value freshMeaning⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeCertificate fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let first ← Tests.SourceCoreDirectFailure.observePublicRun fixture observed
  let next ← observeContinuation (original_first first)
  let fresh ← observeFreshIdentity fixture observed
  have _outcomes := closed_outcomes fixture observed admission failedStages identityStages first next fresh
  IO.println "LEXICAL_SOURCE_OUTCOMES_PASS: original checker1000/compiler100; independent Dynamic uninitialized-location fault retains its allocated absent cell; same session identity37 preserves it; fresh identity37; exact named dictionaries, empty handle histories and all three forward bounds"

end Tests.SourceCoreCertifiedLexicalFailure.SourceOutcomes
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureSeed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver)
    (stages : ObservedStages fixture observed.failedRow)
    (first : ObservedPublicRun fixture observed) :
    ∃ state : RetainedState support first.returned [],
      ∃ failure : Staging.Recursive.Failure,
        SourceCall support support.failedHeader.header
          (RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
          ⟨[]⟩ [] (.fault failure) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := first.start_receipt
  have startupRegistry := first.metadata_at_start opened sessionAt started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.failedHeader.header := by
    apply selected_failed_root support.failedHeader support.identityHeader (root := root)
      (support.header_list ▸ selected)
    exact of_decide_eq_true (List.find?_some
      (p := fun root : SourceCoreIndexedSession.Root fixture.recipe.compiled => decide (root.key = observed.failedRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.failedHeader.header.function.context
      (support.failedHeader.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [support.failedHeader.failed_inputs]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header support.failedInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.failedPacket.header.named.specialized support.failedInput.prepared.available)) := by
    rw [support.failedEq]
    exact support.failedPacket.sourceAt
  obtain ⟨caller, returnedSession, value, finalStore, capture, sourceSize, failure, after,
      finalMap, finalWorld, failed, returnedAt, trace, _fullResult, returnedCaller, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryFailures.public_run_failed_seeds
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
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
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.failedHeader.header.function)
      first.started first.executed support.failedDescriptor
  have returnedRegistry : returnedSession.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases checkpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  rw [startupRegistry] at returnedRegistry
  let state : RetainedState support first.returned [] := {
    artifact := artifact, session := returnedSession, mapping := finalMap, world := finalWorld
    heap := after, store := finalStore, caller := returnedCaller
    atSession := returnedAt, atRecipe := started.recipe_eq, registry := returnedRegistry, history := retained }
  exact ⟨state, failure, support.failedInput.prepared.available, _, sourceSize, sourceAt, trace⟩

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureIssuance
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

def issuanceFuel : Nat := 1024

structure ObservedNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  completion : SourceCoreExecution.Completion artifact
  issued : session.NamedIssuedAt key issuanceFuel completion
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle

def observeNamed {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedNamed session key) := do
  match ← session.namedWithReceipt key issuanceFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok result =>
    match returned : result.val.value with
    | .function handle => pure ⟨result.val, result.property, handle, returned⟩
    | _ => throw (IO.userError "named failure issuance did not return a function")

theorem failed_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.failedPacket.header.named.specialized.function.type = .function .unit .word := by
  obtain ⟨_facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.failedPacket.sourceAt fixture.source_wellFormed
  have bindingTypes : support.failedHeader.header.types = [] := by
    have same := Dynamic.MonoBindersExtend.bodyTypes_eq support.failedHeader.header.extended
    rw [support.failedHeader.header.parameters] at same
    have raw := support.failedHeader.failed_inputs
    simpa only [List.map_map, Function.comp_def, raw] using same.symm
  have shape := certified.callable_type
  change support.failedPacket.header.named.specialized.function.type = _ at shape
  rw [← support.failedPacket.sourceAt.frame.result, ← support.failedEq,
    bindingTypes, support.failedHeader.failed_result_type] at shape
  rw [support.failedEq] at shape
  exact shape

theorem remember_named {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.failedRow.row.key) :
    ∃ (entry : Entry) (global : Dynamic.GlobalFunction),
      entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      entry.source = .global global ∧
      CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header support.failedInput.prepared.available global ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.failedPacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.failedPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.failedEq, support.failedHeader.key]
    exact call.issued
  obtain ⟨actual, native, actualAt, retained⟩ := RecursiveNamedPublicHistoryIssuance.named_remembered
    fixture.recipePrepared [support.failedInput, support.identityInput] support.rows support.failedPacket member
    receiver.completion.result.context.registry receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile state.history state.atRecipe state.atSession issued call.returned fixture.source_wellFormed
  have registry := (call.issued.same_runtime.indexed state.atSession actualAt.2.2.2).registry_at state.registry
  let global := CallableNamedReversal.global (CallableNamedMetadata.global
    support.failedPacket.header.named.specialized support.failedInput.prepared.available)
  let entry : Entry := ⟨support.failedPacket.header.named.specialized.function.type,
    .global global, call.handle, native,
    Core.CallableContract.functionType support.failedPacket.header.named.signature.parameterType
      support.failedPacket.header.named.signature.resultType, issuanceFuel⟩
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header
      support.failedInput.prepared.available global := by
    rw [support.failedEq]
    exact support.failedPacket.sourceAt
  have noParameters : support.failedHeader.header.function.parameters = [] := by
    rw [support.failedHeader.header.parameters, ← support.failedHeader.header.inputs,
      support.failedHeader.source, observed.failedShape.inputs]
  have noInputs : support.failedHeader.header.sourceBody.source.inputs.length = 0 := by
    rw [← sourceAt.frame.parameters, noParameters]
    rfl
  refine ⟨entry, global, failed_source_type support, rfl, rfl, sourceAt,
    noInputs ▸ RecursivePublicCallableArity.Arity.global sourceAt.frame.instantiated,
    ⟨state.artifact, actual.session, state.mapping, state.world, state.heap, state.store, state.caller,
      actualAt.2.2.2, state.atRecipe, registry, retained⟩, rfl⟩

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureInvocation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)

def failureOptions : SourceCoreExecution.RunOptions := { runOptions with outputValidationFuel := 0 }

structure ObservedFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) where
  reason : Core.Word
  returned : SourceCoreExecution.Session artifact
  executed : session.InvokeAt handle .unit failureOptions (.ok (.failed reason returned))

def observeFailure {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle) :
    IO (ObservedFailure session handle) := do
  let executed ← session.invokePackedWithReceipt handle .unit failureOptions
  match result : executed.val with
  | .ok (.failed reason returned) => pure ⟨reason, returned, result ▸ executed.property⟩
  | .error error => throw (IO.userError (reprStr error))
  | _ => throw (IO.userError "direct named call did not fail at output fuel zero")

def ForwardFailureAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (entries : List Entry) (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed,
    CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed receiving.entry
      receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
    ∃ token required,
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
        required ≤ executionFuel → checkpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ returned : SourceCoreExecution.Session artifact,
          outcome = .failed token returned ∧ returned.ExportsReady ∧
          ∃ state : RetainedState support returned entries, state.heap = after

private theorem unit_input {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) (entries : List Entry) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries support.failedHeader.header.function.context
      .unit .unit .unit :=
  .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
    ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩

theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = .function .unit .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {global : Dynamic.GlobalFunction} (entrySource : entry.source = .global global)
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.failedHeader.header
      support.failedInput.prepared.available global)
    (call : ObservedFailure publicSession handle) (ready : publicSession.ExportsReady)
    (invocation : Staging.Recursive.Scope) :
    ∃ (next : RetainedState support call.returned entries) (failure : Staging.Recursive.Failure),
      SourceCall support support.failedHeader.header invocation state.heap [] (.fault failure) next.heap ∧
      ∃ checkpoint : SourceCoreExecution.Checkpoint publicArtifact,
        publicSession.startHandlePacked handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
        ForwardFailureAt support checkpoint entries failure next.heap := by
  have invoked : publicSession.InvokeAt entry.handle .unit failureOptions (.ok (.failed call.reason call.returned)) := by
    rw [entryHandle]
    exact call.executed
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameter, result, nativeParameter, nativeResult, callable, packed, values,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe state.history.current.1 imported original
  have startupRegistry := started.function_tree_registry (.simple .unit) state.registry
  have registry : state.session.RegistryAt receiver.completion.result.context.registry := receiver.registry.symm ▸ state.registry
  obtain ⟨receiving, contextAt, issued, _extended, _diagnostics, actual, value, finalStore,
      sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, returnedAt,
      packing, arity, trace, _result, _related, retained, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryFailures.public_resume_failed_at_arity
      (completion := receiver.completion) receiver.issued (actualStagePrepared fixture) observed.profile
      support.observations (by intro reason token represented; exact represented)
      support.family support.terminals support.supports fixture.source_wellFormed state.history entry member
      entryType (unit_input support entries) registry started atCheckpoint resumed invocation
  have actualRegistry : receiving.result.context.registry = receiver.completion.result.context.registry :=
    (congrArg (·.registry) contextAt).trans (startupRegistry.trans receiver.registry.symm)
  rw [actualRegistry] at retained
  rw [startupRegistry] at returnedRegistry
  let next : RetainedState support call.returned entries :=
    ⟨state.artifact, actual, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  have noParameters : support.failedHeader.header.function.parameters = [] := by
    rw [support.failedHeader.header.parameters, ← support.failedHeader.header.inputs,
      support.failedHeader.source, observed.failedShape.inputs]
  have sourceCount : sources.length = 0 := by
    rw [entrySource] at arity
    have count := arity.global_count fixture.source_wellFormed sourceAt.frame.instantiated
    rw [← sourceAt.frame.parameters, noParameters] at count
    exact count.symm
  have noSources := List.eq_nil_of_length_eq_zero sourceCount
  subst sources
  obtain ⟨receivingForward, contextForward, issuedForward, _extendedForward, _diagnosticsForward,
      required, token, forwardStore, forwardMap, forwardWorld, faultRelated, _enough, _fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryFailurePreservation.public_resume_has_sufficient_fuel
      (completion := receiver.completion) receiver.issued (actualStagePrepared fixture) observed.profile
      support.observations (by intro reason token represented; exact represented)
      support.family support.terminals support.supports fixture.source_wellFormed state.history entry member
      entryType (unit_input support entries) registry (state.atSession.exportsReady_iff.mp ready)
      started packing arity trace atCheckpoint
  refine ⟨next, failure, ⟨support.failedInput.prepared.available, global, sourceSize, sourceAt, ?_⟩,
    publicCheckpoint, ?_, receivingForward, issuedForward, token, required, faultRelated, ?_⟩
  · simpa only [entrySource] using trace
  · simpa only [entryHandle] using accepted
  · intro executionFuel outputFuel outcome bound resumed
    obtain ⟨returned, actual, reached, outcomeEq, _failed, atReturned, _related, history, registry, exportsReady⟩ :=
      publicEnough executionFuel outputFuel outcome bound resumed
    have actualRegistry : receivingForward.result.context.registry = receiver.completion.result.context.registry :=
      (congrArg (·.registry) contextForward).trans (startupRegistry.trans receiver.registry.symm)
    rw [actualRegistry] at history
    rw [startupRegistry] at registry
    exact ⟨returned, outcomeEq, atReturned.exportsReady_iff.mpr exportsReady,
      ⟨state.artifact, actual, forwardMap, forwardWorld, after, forwardStore, reached,
        atReturned, state.atRecipe, registry, history⟩, rfl⟩

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailureSuccess
/-! The actual session returned by the first failed call runs identity(37).
The genuine public result identifies the Source result and retains the same
history at the new session, Source heap and native store. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedSuccess {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key [.word seed] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observeSuccess {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key) :
    IO (ObservedSuccess session key) := do
  match started : session.start key [.word seed] runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key [.word seed] runOptions
    match result : executed.val with
    | .ok (.succeeded completion) =>
      if returned : completion.value = .word seed then
        pure ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "identity after direct failure did not return37")
    | .error error => throw (IO.userError (reprStr error))
    | _ => throw (IO.userError "identity after direct failure did not succeed")

theorem RetainedState.identity {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : RetainedState support session entries)
    (call : ObservedSuccess session observed.identityRow.row.key)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support support.identityHeader.header invocation state.heap [.word seed]
        (.value (.word seed)) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.failedInput, support.identityInput] support.rows support.complete
    state.atRecipe state.history.current.1 state.atSession call.started
  have selectedHeader : request.header = support.identityHeader.header :=
    selected_identity_at support.failedHeader support.identityHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed] [.word seed] := by
    rw [selectedHeader, support.identityHeader.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have registry := request.started.simple_registry state.registry
    (by intro value member; have same := List.mem_singleton.mp member; exact same ▸ SourceCoreIndexedSession.SimplePublic.word seed)
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry receiver.completion.result.context.registry := by
    rw [registry]
    exact receiver.completion.result.extension
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selectedHeader]
    exact support.identityDescriptor
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.failedInput, support.identityInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture)
      (completion := receiver.completion)
      (receiver := receiver.issued)
      (profile := observed.profile) (observations := support.observations)
      (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
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
  rw [resultType, selectedHeader, support.identityHeader.identity_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans call.returned)
    (by rw [selectedHeader]; exact support.identityHeader.identity_output) result
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session entries :=
    ⟨state.artifact, actual.session, finalMap, finalWorld, after, finalStore, reached,
      returnedAt, state.atRecipe, returnedRegistry, retained⟩
  refine ⟨next, request.rawD, request.function, sourceSize, ?_, ?_⟩
  · rw [← selectedHeader]; exact request.sourceAt
  · simpa only [outcomeValue] using trace

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreDirectFailurePublicExecution
/-! The first failed named run seeds the real heap. Named issuance then exposes
that same declared function, a direct packed call fails with output fuel zero,
and identity(37) succeeds in its returned session. Both absent locals survive.
The independently reflected direct Source fault also guarantees actual public
failure at every sufficient execution budget, for every output budget. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed
  named : ObservedNamed first.returned observed.failedRow.row.key
  failed : ObservedFailure named.completion.session named.handle
  next : ObservedSuccess failed.returned observed.identityRow.row.key

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed
  let named ← observeNamed first.returned observed.failedRow.row.key
  let failed ← observeFailure named.completion.session named.handle
  let next ← observeSuccess failed.returned observed.identityRow.row.key
  pure ⟨first, named, failed, next⟩

theorem ObservedPublicRun.returned_exportsReady {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (first : ObservedPublicRun fixture observed) : first.returned.ExportsReady := by
  obtain ⟨_artifact, _session, checkpoint, _root, _world, _store, _native, _values,
      _opened, _prepared, atSession, atCheckpoint, started⟩ := first.start_receipt
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := first.executed
  have same : publicCheckpoint = first.checkpoint := Except.ok.inj (accepted.symm.trans first.started)
  subst publicCheckpoint
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ := resumed.indexed_failed atCheckpoint
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single first.ready).exportsReady first.authority
  exact returnedAt.exportsReady_iff.mpr
    (failed.exportsReady (started.original.initial_registry.exportsReady (atSession.exportsReady_iff.mp ready)))

/-- All program, input, declared arity and reached-state conditions come from
this compiler and these real public events. No Source trace is a premise. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
      let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
      ∃ (initial : RetainedState support sequence.first.returned []) (entry : Entry)
        (issued : RetainedState support sequence.named.completion.session [entry])
        (failed : RetainedState support sequence.failed.returned [entry])
        (final : RetainedState support sequence.next.completion.session [entry])
        (firstLocation secondLocation parameterLocation : Dynamic.Location),
        entry.sourceType = .function .unit .word ∧ entry.handle = sequence.named.handle ∧
        RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram) entry.source 0 ∧
        Dynamic.Heap.Allocates ⟨[]⟩ .word none firstLocation initial.heap ∧ issued.heap = initial.heap ∧
        Dynamic.Heap.Allocates issued.heap .word none secondLocation failed.heap ∧
        Dynamic.Heap.Allocates failed.heap .word (some (.word seed)) parameterLocation final.heap ∧
        Dynamic.Heap.Reads final.heap firstLocation { type := .word, value := none } ∧
        Dynamic.Heap.Reads final.heap secondLocation { type := .word, value := none } ∧
        SourceCall support support.failedHeader.header failedScope ⟨[]⟩ []
          (.fault (.semantic (.uninitializedLocation firstLocation))) initial.heap ∧
        SourceCall support support.failedHeader.header failedScope issued.heap []
          (.fault (.semantic (.uninitializedLocation secondLocation))) failed.heap ∧
        SourceCall support support.identityHeader.header identityScope failed.heap [.word seed]
          (.value (.word seed)) final.heap ∧
        ∃ checkpoint : SourceCoreExecution.Checkpoint sequence.first.artifact,
          sequence.named.completion.session.startHandlePacked sequence.named.handle .unit failureOptions.inputValidationFuel = .ok checkpoint ∧
          ForwardFailureAt support checkpoint [entry] (.semantic (.uninitializedLocation secondLocation)) failed.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed failedStages identityStages
    receiver.completion.result.context.registry receiver.issued
  let failedScope := RecursiveStageRegistry.scope failedStages.sidecar [] support.failedHeader.header.function
  let identityScope := RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function
  obtain ⟨initial, firstFailure, firstCall⟩ := first_meaning support failedStages sequence.first
  obtain ⟨firstD, firstGlobal, firstSize, firstAt, firstTrace⟩ := firstCall
  obtain ⟨firstLocation, firstEq, firstAllocated, firstAbsent⟩ := support.failedHeader.failed_heap firstAt firstTrace
  obtain ⟨entry, global, entryType, entryHandle, entrySource, sourceAt, arity, issued, issuedHeap⟩ :=
    remember_named initial sequence.named
  have ready := sequence.named.issued.exportsReady sequence.first.returned_exportsReady
  obtain ⟨failed, secondFailure, failedCall, checkpoint, started, forward⟩ :=
    invoke issued entry (by simp) entryType entryHandle entrySource sourceAt sequence.failed ready failedScope
  obtain ⟨secondD, secondGlobal, secondSize, secondAt, secondTrace⟩ := failedCall
  obtain ⟨secondLocation, secondEq, secondAllocated, secondAbsent⟩ := support.failedHeader.failed_heap secondAt secondTrace
  obtain ⟨final, nextCall⟩ := failed.identity sequence.next identityScope
  obtain ⟨identityD, identityGlobal, identitySize, identityAt, identityTrace⟩ := nextCall
  obtain ⟨parameterLocation, parameterAllocated⟩ := support.identityHeader.identity_heap identityAt identityTrace
  have firstKept : Dynamic.Heap.Reads final.heap firstLocation { type := .word, value := none } :=
    parameterAllocated.preserves_read (secondAllocated.preserves_read (issuedHeap.symm ▸ firstAbsent))
  refine ⟨receiver, support, initial, entry, issued, failed, final, firstLocation, secondLocation, parameterLocation,
    entryType, entryHandle, arity, firstAllocated, issuedHeap, secondAllocated, parameterAllocated,
    firstKept, parameterAllocated.preserves_read secondAbsent, ?_, ?_, ?_, checkpoint, started, ?_⟩
  · exact ⟨firstD, firstGlobal, firstSize, firstAt, firstEq ▸ firstTrace⟩
  · exact ⟨secondD, secondGlobal, secondSize, secondAt, secondEq ▸ secondTrace⟩
  · exact ⟨identityD, identityGlobal, identitySize, identityAt, identityTrace⟩
  · exact secondEq ▸ forward

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let failedStages ← observeStages fixture observed.failedRow
  let identityStages ← observeStages fixture observed.identityRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed failedStages identityStages sequence
  IO.println "Actual direct named failure: output fuel0, Source arity and sufficient-fuel failure, two absent cells retained through identity37 proved"

end Tests.SourceCoreDirectFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalFailureProfile
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure

def observeProfile (fixture : CompiledFixture) :
    IO (CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled) := do
  have checked : checkProgram _ _ = .ok fixture.recipe.compiled.sourceProgram := by
    rw [fixture.sameProgram]
    exact fixture.checked
  let some profile := SelectedCompilationCompilerStaticProfile.validateCheckedProfile fixture.recipe.compiled checked
    | throw (IO.userError "selected lexical profile rejected")
  pure profile

end Tests.SourceCoreSelectedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalFailureMeaning
/-! The unchanged lexical program uses one automatically issued physical
session after its first failure, then continues with identity(37). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreCertifiedLexicalFailure (First FreshIdentity first_call original_first continuation_call first_returned_ready eligible_row header_of_member header_types)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) where
  initial : Initial issued.toIssued (first_call first)
  actual : ActualHeader fixture observed.failedRow.row
  headerEq : initial.header = actual.header
  after : issued.toIssued.State initial.header first.returned []
  location : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word none location after.heap
  absent : Dynamic.Heap.Reads after.heap location {type := .word, value := none}
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
    (.fault (.semantic (.uninitializedLocation location))) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainFault initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
    (.uninitializedLocation location) after.heap
  decoded : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
    (.semantic (.uninitializedLocation location)) first.reason
  forward : SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.semantic (.uninitializedLocation location)) (first_call first) after.heap

structure ContinuationMeaning {issued : Profiled fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    next.checkpoint before.after.session observed.identityRow.row.key [.word seed]
    runOptions.inputValidationFuel before.after.world before.after.store
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : request.header = actual.header
  after : issued.toIssued.State before.initial.header next.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates before.after.heap .word (some (.word seed)) parameter after.heap
  absent : Dynamic.Heap.Reads after.heap before.location {type := .word, value := none}
  trace : SourceCall before.initial.header request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
    (.value (.word seed)) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows before.initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) (continuation_call next).toStartedCall after.heap

structure FreshMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) where
  initial : Initial issued.toIssued fresh.call.toStartedCall
  actual : ActualHeader fixture observed.identityRow.row
  headerEq : initial.header = actual.header
  after : issued.toIssued.State initial.header fresh.call.completion.session []
  parameter : Dynamic.Location
  allocated : Dynamic.Heap.Allocates ⟨[]⟩ .word (some (.word seed)) parameter after.heap
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
    (.value (.word seed)) after.heap
  plain : RecursiveNamedPublicPhysicalSessionState.PlainValue initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
    (.word seed) after.heap
  forward : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [])
    issued.catalog.rows initial.header issued.initial issued.support.profile fixture.recipe
    (.word seed) fresh.call.toStartedCall after.heap

theorem first_meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.failedRow) (first : First fixture observed) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.failedRow
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile first.opened
    (first_call first) first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.failedRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [] initial.header.types := by
    rw [header_types, ← actualEq, actual.failed_inputs]
    exact .nil
  have simple : ∀ value ∈ ([] : List SourceCorePublicValues.Value), SourceCoreIndexedSession.SimplePublic value := by
    intro value member; cases member
  obtain ⟨failure, after, trace, plain, decoded⟩ := SelectedCompilationCertifiedPublicSession.Profiled.reflect_initial_failure_plain initial first.returned first.reason first.executed
    simple inputTypes .nil (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨location, failureEq, allocated, absent⟩ := actual.failed_heap
    (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ []
      (.fault (.semantic (.uninitializedLocation location))) after.heap :=
    ⟨rawD, global, size, sourceAt, failureEq ▸ applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, location, allocated, absent,
    sourceCall, (by simpa only [failureEq, RecursiveNamedPublicPhysicalSessionState.FailureProjection] using plain), failureEq ▸ decoded, SelectedCompilationCertifiedPublicSession.Profiled.forward_initial_failure initial simple inputTypes .nil sourceCall⟩⟩⟩

theorem continuation_meaning {issued : Profiled fixture.recipe}
    {failedStages : ObservedStages fixture observed.failedRow} {first : First fixture observed}
    (before : FirstMeaning issued failedStages first)
    (stages : ObservedStages fixture observed.identityRow)
    (next : ObservedContinuation (original_first first)) :
    Nonempty (ContinuationMeaning before stages next) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before.after (continuation_call next).toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word seed] [.word seed] := by
    rw [← actualEq, actual.identity_inputs]
    exact .cons (.data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩) .nil
  have raw : request.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : request.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := issued.toIssued.reflect_scalar before.after (.word seed) (continuation_call next)
    next.returned request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall before.initial.header request.header
      (RecursiveStageRegistry.scope stages.sidecar [] request.header.function) before.after.heap [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  have ready : first.returned.ExportsReady := first_returned_ready first
  exact ⟨⟨request, actual, actualEq.symm, after, parameter, allocated,
    allocated.preserves_read before.absent, sourceCall,
    issued.toIssued.forward_scalar before.after (.word seed) (continuation_call next).toStartedCall request
      inputs raw native ready sourceCall⟩⟩

theorem fresh_meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow) (fresh : FreshIdentity fixture observed) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FreshMeaning issued stages fresh) := by
  obtain ⟨row, sameRow⟩ := eligible_row observed.identityRow
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile fresh.opened
    fresh.call.toStartedCall fresh.bootstrap fresh.fresh fresh.authority
    (show fresh.bootstrap.ReadyAt 100000 fresh.session from .single fresh.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.identityRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [header_types, ← actualEq, actual.identity_inputs]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have simple : ∀ value ∈ [.word seed], SourceCoreIndexedSession.SimplePublic value := by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact .word seed
  have raw : initial.header.function.resultType = .word := by rw [← actualEq]; exact actual.identity_result_type
  have native : initial.header.output = .word := by rw [← actualEq]; exact actual.identity_output
  obtain ⟨after, trace⟩ := initial.reflect_scalar (.word seed) fresh.returned simple inputTypes inputMeanings
    raw native (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  obtain ⟨parameter, allocated⟩ := actual.identity_heap (actualEq.symm ▸ sourceAt) applied
  have sourceCall : SourceCall initial.header initial.header
      (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function) ⟨[]⟩ [.word seed]
      (.value (.word seed)) after.heap := ⟨rawD, global, size, sourceAt, applied⟩
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, after, parameter, allocated, sourceCall, sourceCall.value_plain,
    initial.forward_scalar (.word seed) simple inputTypes inputMeanings raw native sourceCall⟩⟩⟩

end Tests.SourceCoreSelectedLexicalFailure
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalOrdinaryTraces
/-! Ordinary executions of the existing lexical program are constructed from
its original source nodes and fresh allocations, before any public execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalOrdinaryTraces
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def appendWord (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := .word, value := value }]⟩

def nextLocation (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩

theorem ActualHeader.identity_plain
    (actual : ActualHeader fixture observed.identityRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Core.Word) :
    PlainValue anchor actual.header invocation before [.word value] (.word value)
      (appendWord before (some (.word value))) := by
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  have allocated : Dynamic.Heap.Allocates before observed.identityShape.binder.scheme.body
      (some (.word value)) (nextLocation before) (appendWord before (some (.word value))) := by
    rw [observed.identityShape.binderScheme]
    exact .append
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [.word value]
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value))) := by
    rw [parameters]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      observed.identityShape.read.id (.word value) (appendWord before (some (.word value))) := by
    apply Dynamic.ExpressionEvaluates.intro
      (lookupExpression?_sound (actual.source.symm ▸ observed.identityShape.readFound))
    · rw [observed.identityShape.readForm]
      exact .local (by rw [observed.identityShape.readRequirements, observed.identityShape.readCoercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [observed.identityShape.readCoercions]; exact .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      actual.header.function.body actual.header.context (.returned (.word value))
      (appendWord before (some (.word value))) := by
    rw [actual.identity_statements]
    have found := lookupStatement?_sound (actual.source.symm ▸ observed.identityShape.statementFound)
    exact .singleton found (by rw [observed.identityShape.statementForm]; intro expression impossible; cases impossible)
      (.returnValue found observed.identityShape.statementForm read)
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.returned executed)
  cases body with
  | value invoked =>
    refine ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl ?_ ?_⟩
    · exact sourceAt.dictionary ▸ sourceAt.frame.covers
    · exact sourceAt.dictionary ▸ invoked

private theorem failed_extension (actual : ActualHeader fixture observed.failedRow.row) :
    ∃ finalContext, BinderExtends actual.header.function.source.owner actual.header.context
      observed.failedShape.binder finalContext := by
  obtain ⟨facts, final, typed, roots, complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.failedShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  have unique : NodeOccurrencesUnique observed.failedRow.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | cons head tail =>
    cases head with
    | letUninitialized contains form mono generalized extended type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.declaredFound)
      cases same
      rw [observed.failedShape.declaredForm] at form
      cases (StatementForm.letDecl.inj form).1
      exact ⟨_, actual.source.symm ▸ extended⟩
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.declaredFound)
      cases same
      simp_all [observed.failedShape.declaredForm]

theorem ActualHeader.failed_plain
    (actual : ActualHeader fixture observed.failedRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    PlainFault anchor actual.header invocation before [] (.uninitializedLocation (nextLocation before))
      (appendWord before none) := by
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [] [] before := by
    rw [parameters]; exact .nil _ _
  have allocated : Dynamic.Heap.Allocates before observed.failedShape.binder.scheme.body none
      (nextLocation before) (appendWord before none) := by
    rw [observed.failedShape.binderScheme]; exact .append
  obtain ⟨finalContext, extension⟩ := failed_extension actual
  have read : Dynamic.ExpressionFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      finalContext actual.header.function.evidence actual.header.function.source
      [(observed.failedShape.binder.id, nextLocation before)] (appendWord before none)
      observed.failedShape.read.id (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    apply Dynamic.ExpressionFaults.form
      (lookupExpression?_sound (actual.source.symm ▸ observed.failedShape.readFound))
    rw [observed.failedShape.readForm]
    apply Dynamic.ExpressionFormFaults.localUninitialized (owned := [])
      (cell := {type := observed.failedShape.binder.scheme.body, value := none})
      (by rw [observed.failedShape.readRequirements, observed.failedShape.readCoercions]; rfl)
      .head allocated.reads_new rfl rfl
    rw [observed.failedShape.binderScheme]
    intro ⟨key, value, impossible⟩
    cases impossible
  have executed : Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source [] before
      actual.header.function.body finalContext (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    rw [actual.failed_statements]
    exact .tail
      (.letUninitialized (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.declaredFound))
        observed.failedShape.declaredForm (by rw [observed.failedShape.binderScheme]; rfl) extension allocated)
      (.singleton (.returnValue (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.statementFound))
        observed.failedShape.statementForm read))
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.fault executed)
  cases body with
  | fault failed =>
    exact ⟨rawD, global, sourceAt, .globalBody sourceAt.frame.instantiated rfl (sourceAt.dictionary ▸ failed)⟩

end Tests.SourceCoreSelectedLexicalOrdinaryTraces
end

section
-- leanmerge: from Solcore.Test.SourceCoreSelectedLexicalSourceStart
/-! This observer stops at the public call checkpoint. No execution result is
stored or required to construct its automatically issued initial session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreSelectedLexicalSourceStart
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure Started (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  call : RecursiveNamedPublicPhysicalSessionState.StartedCall session key arguments runOptions

def observeStarted (fixture : CompiledFixture) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) : IO (Started fixture key arguments) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "lexical source bootstrap exhausted")
  | .ready session =>
    match started : session.start key arguments runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2,
        session, ready, checkpoint, started⟩

theorem initial {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (row : ObservedRow fixture signature) {arguments : List SourceCorePublicValues.Value}
    (started : Started fixture row.row.key arguments) :
    ∃ issued : Profiled fixture.recipe, ∃ first : Initial issued.toIssued started.call,
      ∃ actual : ActualHeader fixture row.row, actual.header = first.header := by
  obtain ⟨selected, sameRow⟩ := Tests.SourceCoreCertifiedLexicalFailure.eligible_row row
  obtain ⟨issued, first, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_checked_profiled_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile started.opened started.call started.bootstrap started.fresh started.authority
    (show started.bootstrap.ReadyAt 100000 started.session from .single started.ready) selected
  obtain ⟨actual, actualEq⟩ := Tests.SourceCoreCertifiedLexicalFailure.header_of_member row issued.catalog.rows
    first.start.selected.member ((congrArg (·.specialized) namedEq).trans sameRow)
  exact ⟨issued, first, actual, actualEq⟩


theorem failed_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row) : actual.header.types = [] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  simpa only [parameters, List.map_nil] using types.symm

theorem identity_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.types = [.word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  simpa only [parameters, List.map_cons, List.map_nil, observed.identityShape.binderScheme,
    TypeSystem.Scheme.mono] using types.symm

theorem identity_result {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.function.resultType = .word := by
  obtain ⟨facts, final, typed, roots, complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.identityShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  have unique : NodeOccurrencesUnique observed.identityRow.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | singleton last =>
    cases last with
    | returnValue contains form expression type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.identityShape.statementFound)
      cases same
      exact type.symm.trans observed.identityShape.statementType
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.identityShape.statementFound)
      cases same
      simp_all [observed.identityShape.statementForm]

theorem identity_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [identity_result actual] at projected
  exact (Except.ok.inj projected).symm

end Tests.SourceCoreSelectedLexicalSourceStart
end
