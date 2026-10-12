import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicEmptyInputRegistry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
set_option autoImplicit false
set_option Elab.async false
/-! A concrete parsed program is independently Source-typed, compiled, opened
and run through the public API. Real compiler receipts construct its complete
static family, and the public theorem produces a Source application and the
returned function-handle history. No body law or value representation is an
input to the fixture. This case is an empty unit lambda, without captures. -/
namespace Tests.SourceCoreClosedLambdaPublicExecution
open Solcore Frontend SourceInference SourceSemantics

/-- Decidable observations of the actual checked factory. Deep Source typing
is constructed from these observations instead of assumed from checker success. -/
structure UnitFactoryShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  expression : ExpressionNode
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = []
  returns : signature.returnTypes = [.function .unit .unit]
  inputs : function.typedBody.inputs = []
  roots : function.typedBody.roots = [.statement statement.id]
  expressionFound : function.typedBody.lookupExpression? expression.id = some expression
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  lambda : expression.form = .lambda [] .unit []
  expressionRaw : expression.rawType = .function .unit .unit
  expressionType : expression.type = .function .unit .unit
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  returnStatement : statement.form = .returnStmt (some expression.id)
  statementType : statement.type = .function .unit .unit

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

/-- Empty lambda bodies really have unit type in the lexical context of this
actual outer return. No runtime or compiler meaning law enters this proof. -/
theorem UnitFactoryShape.statementTyping
    {function : CheckedFunction} {signature : ProgramFunctionSignature}
    (shape : UnitFactoryShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] :=
    statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {
    type := .function .unit .unit
    hasValue := true
    sawReturn := true
    control := .returned }
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension
  have binders : TypeParameterBindersWellFormed
      (checkedBodyContext signatures signature function) := by
    simp [TypeParameterBindersWellFormed, checkedBodyContext, declarationContext,
      Context.ofSignatures, Context.forDeclaration,
      Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
  have admissible : TypeAdmissible (checkedBodyContext signatures signature function)
      (.function .unit .unit) := ⟨binders, .function (.builtin .unit) (.builtin .unit)⟩
  have expressionTyped : ExpressionHasType function.typedBody
      (checkedBodyContext signatures signature function) shape.expression.id
      (.function .unit .unit) := by
    rw [← shape.expressionType]
    refine .intro (lookupExpression?_sound shape.expressionFound)
      (shape.lambda ▸ ExpressionFormHasRawType.lambda (by simp) (.nil _)
        (.nil _ _) (by exact ⟨rfl, rfl, .inr rfl⟩)) shape.expressionRaw
      admissible (shape.expressionType ▸ admissible) ?_
    rw [shape.requirements, shape.coercions, shape.expressionType]
    exact .ordinary (by intro id member; cases member) (.nil _) rfl
  exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
    shape.returnStatement expressionTyped shape.statementType)⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  externalLibraries := []
  mainSources := [{path := "main.solc", content :=
    "function make() returns (function() returns ()) { return lam() {}; }"}] }

private def shape (function : CheckedFunction) (signature : ProgramFunctionSignature) :
    IO (UnitFactoryShape function signature) := do
  let [Node.expression expression, Node.statement statement] := function.typedBody.nodes
    | throw (IO.userError "unit factory occurrence shape")
  if observed : signature.scheme.parameters = [] ∧ signature.parameterTypes = [] ∧
      signature.returnTypes = [.function .unit .unit] ∧ function.typedBody.inputs = [] ∧
      function.typedBody.roots = [.statement statement.id] ∧
      function.typedBody.lookupExpression? expression.id = some expression ∧
      function.typedBody.lookupStatement? statement.id = some statement ∧
      expression.form = .lambda [] .unit [] ∧ expression.rawType = .function .unit .unit ∧
      expression.type = .function .unit .unit ∧ expression.requirements = [] ∧ expression.coercions = [] ∧
      statement.form = .returnStmt (some expression.id) ∧ statement.type = .function .unit .unit then
    return ⟨expression, statement, observed.1, observed.2.1, observed.2.2.1,
      observed.2.2.2.1, observed.2.2.2.2.1, observed.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2.2.2.2.2.2.1,
      observed.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  else throw (IO.userError "unit factory retained source metadata")

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  function : CheckedFunction
  signature : ProgramFunctionSignature
  functions : program.functions = [function]
  signatures : program.signatures.functions = [signature]
  methods : program.methods = []
  sourceShape : UnitFactoryShape function signature
  nodes : function.typedBody.nodes = [.expression sourceShape.expression, .statement sourceShape.statement]

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [function], [signature] =>
      let sourceShape ← shape function signature
      if methods : program.methods = [] then
        let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
          functions := by
            intro actual member candidate candidateMember _accepted
            have sameFunction : actual = function := by simpa only [functions, List.mem_singleton] using member
            have sameSignature : candidate = signature := by simpa only [signatures, List.mem_singleton] using candidateMember
            subst actual candidate
            exact sourceShape.statementTyping program.signatures
          methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
        if nodes : function.typedBody.nodes = [.expression sourceShape.expression, .statement sourceShape.statement] then
          return ⟨program, checked, programWellFormed_ofCheckProgram_statements checked deep,
            function, signature, functions, signatures, methods, sourceShape, nodes⟩
        else throw (IO.userError "factory complete node graph changed")
      else throw (IO.userError "unexpected unit factory methods")
    | _, _ => throw (IO.userError "unit factory declaration count")


structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program

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
            sameProgram := sameProgram }

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



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
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
  exact ⟨terminal, rfl, rfl⟩


/-- Finite, executable checks of the same actual compiled row. None is an
execution correspondence or a supplied lambda formation certificate. -/
structure ObservedFactory (fixture : CompiledFixture) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  parameters : row.parameterSubstitution = []
  closed : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputs : row.function.typedBody.inputs = []
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedMetadata.instantiation row) = .ok row.key
  expression : ExpressionNode
  statement : StatementNode
  roots : row.function.typedBody.roots = [.statement statement.id]
  foundStatement : row.function.typedBody.lookupStatement? statement.id = some statement
  returnStatement : statement.form = .returnStmt (some expression.id)
  foundExpression : row.function.typedBody.lookupExpression? expression.id = some expression
  nodes : row.function.typedBody.nodes = [.expression expression, .statement statement]
  lambda : expression.form = .lambda [] .unit []
  owned : expression.id.occurrence.owner = row.function.typedBody.owner
  requirements : expression.requirements = []
  coercions : expression.coercions = []
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  noNativeInputs : entry.native.inputTypes = []
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
    row.function.typedBody expression.id = .ok (expression, reported)

def observeFactory (fixture : CompiledFixture) : IO (ObservedFactory fixture) := do
  match rows : fixture.recipe.compiled.validationPlan.specializations with
  | [row] =>
    match target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
        (CallableNamedMetadata.instantiation row) with
    | .error _ => throw (IO.userError "factory exact target")
    | .ok key =>
      if shape : row.parameterSubstitution = [] ∧ row.assumptions = [] ∧
          row.function.returnComptime = false ∧ row.function.typedBody.inputs = [] ∧ key = row.key then
        let [Node.expression expression, Node.statement statement] := row.function.typedBody.nodes
          | throw (IO.userError "factory occurrence list")
        if observed : row.function.typedBody.roots = [.statement statement.id] ∧
            row.function.typedBody.lookupStatement? statement.id = some statement ∧
            statement.form = .returnStmt (some expression.id) ∧
            row.function.typedBody.lookupExpression? expression.id = some expression ∧
            expression.form = .lambda [] .unit [] ∧ expression.id.occurrence.owner = row.function.typedBody.owner ∧
            expression.requirements = [] ∧ expression.coercions = [] ∧
            fixture.recipe.compiled.indexed.base.locals.bindings = [] ∧
            fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true then
          match entries : fixture.recipe.compiled.indexed.entries with
          | [entry] =>
            if noNativeInputs : entry.native.inputTypes = [] then
              match read : SourceCoreCompatibleDataExpressions.readExpression fixture.recipe.compiled.compatible.checked
                  row.function.typedBody expression.id with
              | .error _ => throw (IO.userError "factory actual expression reader")
              | .ok (node, reported) =>
                if same : node = expression then
                  if nodes : row.function.typedBody.nodes = [.expression expression, .statement statement] then
                    return {
                      row := row
                      member := by rw [rows]; exact .head []
                      parameters := shape.1
                      closed := shape.2.1
                      ordinary := shape.2.2.1
                      inputs := shape.2.2.2.1
                      target := by rw [target, shape.2.2.2.2]
                      expression := expression
                      statement := statement
                      roots := observed.1
                      foundStatement := observed.2.1
                      returnStatement := observed.2.2.1
                      foundExpression := observed.2.2.2.1
                      nodes := nodes
                      lambda := observed.2.2.2.2.1
                      owned := observed.2.2.2.2.2.1
                      requirements := observed.2.2.2.2.2.2.1
                      coercions := observed.2.2.2.2.2.2.2.1
                      noLocals := observed.2.2.2.2.2.2.2.2.1
                      profile := observed.2.2.2.2.2.2.2.2.2
                      entry := entry
                      entryMember := by rw [entries]; exact .head []
                      noNativeInputs := noNativeInputs
                      reported := reported
                      read := by rw [read, same] }
                  else throw (IO.userError "factory full specialized node graph changed")
                else throw (IO.userError "factory reader changed source node")
            else throw (IO.userError "factory has native inputs")
          | _ => throw (IO.userError "factory native entry count")
        else throw (IO.userError "factory retained source observations")
      else throw (IO.userError "factory retained row observations")
  | _ => throw (IO.userError "factory row count")


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
    ordinaryParameters := by intro binder member; simp only [observed.inputs, List.not_mem_nil] at member
    target := target
    slot := by simp only [CallableNamedMetadata.Slot, globals, zero]; simp }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := by simpa only [input, metadata] using packet.aligned }
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

theorem ObservedFactory.only_lambda {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (found : observed.row.function.typedBody.lookupExpression? id = some node) :
    node.form = .lambda [] .unit [] := by
  have member := (lookupExpression?_sound found).1
  rw [observed.nodes] at member
  have same : node = observed.expression := by
    rcases List.mem_cons.mp member with same | rest
    · exact Node.expression.inj same
    · rcases List.mem_cons.mp rest with impossible | empty
      · cases impossible
      · cases empty
  exact same ▸ observed.lambda

theorem ObservedStages.association_empty {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping}
    {function : Dynamic.Closure} {native : Core.Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys registry faults
      mapping world function native bindings parameterCore resultCore) :
    function.body = [] ∧ function.resultType = .unit := by
  have fromSource {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (code : CallableIndexedLambdaValues.Code fixture.recipe.compiled.indexed function scope administrative)
      (sameSource : function.source = observed.row.function.typedBody) :
      function.body = [] ∧ function.resultType = .unit := by
    have found := code.sourceFound
    rw [sameSource] at found
    have form := (observed.only_lambda found).symm.trans code.sourceForm
    exact ⟨(ExpressionForm.lambda.inj form).2.2.symm, (ExpressionForm.lambda.inj form).2.1.symm⟩
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ =>
    exact fromSource code (support.source.trans (stages.source_of_cached actual support.caller.selected))
  | principal _ _ code _ support _ _ _ _ _ _ =>
    exact fromSource code (support.source.trans (stages.source_of_cached actual support.principal.cached.selected))


theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

theorem ActualHeader.formation {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (expression : terminal.expression = observed.expression.id)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedContextualLambdaFormationReceipts.OrdinaryFormation
      (registry := registry) (faults := faults) actual.header actual.header.context
      actual.header.function.evidence
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  apply CallableIndexedOwnedPreparedNamedEmptyLambdaFormation.of_terminal terminal
    fixture.source_wellFormed observed.profile (stages.selected actual)
    observed.entryMember observed.noNativeInputs
    (node := observed.expression) (reported := observed.reported)
  · rw [actual.source, expression]; exact observed.foundExpression
  · exact observed.lambda
  · rw [actual.source, expression]; exact observed.owned
  · exact observed.requirements
  · exact observed.coercions
  · simp only [observed.noLocals, List.find?_nil]
  · rw [actual.source, expression]; exact observed.read

theorem ActualHeader.support {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header)
    (expression : terminal.expression = observed.expression.id)
    (point : terminal.certificate = CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBodySupport.Support
      [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header stages.registry terminal faults) := by
  obtain ⟨formation⟩ := actual.formation stages terminal expression
  exact ⟨.formation (CallableIndexedOwnedPreparedStagedNamedBodySupport.Formation.of_actual
    [actual.header] (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    registry actual.header stages.registry terminal faults point (actual.complete stages)
    (bootstrap_zero fixture.recipe.compiled) formation fixture.source_wellFormed)⟩


theorem ActualHeader.no_bindings {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) : actual.header.bindings = [] := by
  have inputs := actual.header.inputs
  rw [actual.source, observed.inputs] at inputs
  exact List.map_eq_nil_iff.mp inputs.symm

def ActualHeader.descriptor {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

private def runOptions : SourceCoreExecution.RunOptions := {
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
  started : session.start observed.row.key [] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [] runOptions (.ok (.succeeded completion))
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
    match started : session.start observed.row.key [] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [] runOptions
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
  executed : fixture.recipe.compiled.indexed.runSource observed.row.key []
    runOptions.executionFuel runOptions.inputValidationFuel = .ok completion

def observeReceiver (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedReceiver fixture observed) := do
  match executed : fixture.recipe.compiled.indexed.runSource observed.row.key []
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
      RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [] runOptions.inputValidationFuel
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
    (started : RecursiveNamedPublicStartMeaning.StartAt session observed.row.key [] runOptions.inputValidationFuel
      checkpoint fixture.recipe root world store native encodedValues) :
    encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
  have ready : executed.bootstrap.ReadyAt 100000 executed.session := .single executed.ready
  obtain ⟨bootstrap, initialized, value, initialStore, _atBootstrap, initial, initializedAt, _done, booted⟩ :=
    ready.indexed opened executed.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  exact started.empty_registry (booted.registry_at initial)


/-- A closed fixture conclusion retains an independent Source application and
an actual returned-session history for the handle observed from the public API. -/
def PublicFactoryMeaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (executed : ObservedPublicRun fixture observed)
    (receiver : ObservedReceiver fixture observed) : Prop :=
  let compiled := fixture.recipe.compiled
  let keys := CallableIndexedOwnedPreparedBootstrapRootState.keys compiled
  let registry := receiver.completion.result.context.registry
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
  ∃ actual : ActualHeader fixture observed.row,
    ∃ headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)),
    actual.header ∈ headers ∧
    ∃ (rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment) (function : Dynamic.GlobalFunction),
    CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD function ∧
    ∃ (sourceSize : Nat) (source : Dynamic.Value) (after : Dynamic.Heap),
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages.registry sourceSize
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function)
      actual.header.function.context ⟨[]⟩ (.global function) [] (.value source) after ∧
    ∃ (artifact : SourceCoreIndexedSession.Artifact) (session : SourceCoreIndexedSession.Session artifact)
      (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store) (payload : Core.Value),
    ∃ caller : RecursiveNamedPublicFunctionHistory.Caller headers keys mapping world after store,
      executed.completion.session.IndexedAt session ∧
      RecursiveNamedPublicFunctionHistory.History headers keys
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys registry faults observed.profile)
        registry actual.header session mapping world after store caller
        [⟨actual.header.function.resultType, source, executed.handle, payload, actual.header.output,
          runOptions.outputValidationFuel⟩]

/-- All public theorem premises are produced by the actual checker/compiler,
bootstrap, encoder and run receipts of this fixture. No representation,
execution correspondence, static body certificate or family is supplied. -/
theorem public_factory_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (executed : ObservedPublicRun fixture observed)
    (receiver : ObservedReceiver fixture observed) :
    PublicFactoryMeaning fixture observed stages executed receiver := by
  obtain ⟨input, _row, packet, actual, sameHeader⟩ := stages.inventory
  let rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory [input] := .cons packet .nil
  have headerList : CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows = [actual.header] := by
    simp only [rows, CallableIndexedOwnedPreparedFiniteNamedInventories.headers, sameHeader]
  let stagePrepared := RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected
  let registry := receiver.completion.result.context.registry
  let faults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
  obtain ⟨terminal, expression, point⟩ := actual.terminal observed.expression.id observed.statement
    observed.roots observed.foundStatement observed.returnStatement
  obtain ⟨support⟩ := actual.support stages terminal expression point (registry := registry) (faults := faults)
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
    have shape := stages.association_empty actual association
    exact .empty shape.1 shape.2
  have observations : CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      (CallableIndexedOwnedContextualCellOrigins.functions
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults observed.profile)
      (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
    intro metadata mapping world sourceType source native type origin
    exact CallableIndexedOwnedGeneralLambdaValues.observations _ registry faults observed.profile
      (registry := metadata) (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := executed.start_receipt
  have complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) := by
    rw [headerList]
    exact actual.complete stages
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared complete
  have selectedEq : selectedHeader = actual.header := by
    have member := selected.member
    rw [headerList] at member
    exact List.mem_singleton.mp member
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs rows session actual.header.function.context
      (actual.header.bindings.map (fun binding => binding.1.scheme.body)) [] [] := by
    rw [actual.no_bindings]
    exact .nil
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry := by
    rw [executed.metadata_at_start opened sessionAt started]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header input.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)) := by
    rw [sameHeader]
    exact packet.sourceAt
  obtain ⟨caller, returnedCompletion, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, typeEq, budgetEq, returnedAt, trace, fullResult,
      returnedCaller, source, payload, sourceValue, nativeValue, related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_remembers
      (inputs := [input]) (rows := rows) (distinct := by simp)
      (stagePrepared := stagePrepared)
      (receiver := CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
      (profile := observed.profile) (bodyRegistry := registry) (semanticFaults := faults)
      (observations := observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := family) (namedTerminals := terminals) (namedSupport := supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := executed.fresh) (ready := .single executed.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl executed.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] actual.header.function)
      executed.started executed.executed executed.returned (actual.descriptor stages)
  exact ⟨actual, CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows,
    by rw [headerList]; exact .head [], input.prepared.available, _, sourceAt,
    sourceSize, source, after, sourceValue ▸ trace, artifact, returnedCompletion.session,
    finalMap, finalWorld, finalStore, payload, returnedCaller, returnedAt, retained⟩

def run : IO Unit := do
  let certified ← compiledFixture
  let observed ← observeFactory certified
  let stages ← observeStages certified observed
  let executed ← observePublicRun certified observed
  let receiver ← observeReceiver certified observed
  have _publicMeaning := public_factory_meaning certified observed stages executed receiver
  IO.println "Actual compiled unit lambda factory: Source application and exported-handle history proved through public execution"

end Tests.SourceCoreClosedLambdaPublicExecution
