import Solcore.Test.SourceCoreMethodClosureSource
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics

private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
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
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id,
    SourceCompiler.Seed.declaration checked.useWordSignature.id, SourceCompiler.Seed.declaration checked.useBoolSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1024, compilationFuel := 1000, specializationBudget := 256}
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
    (CoreLowering.CallableNamedCanonicalOrder.retainedInstantiation row) header
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
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row
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
and original source declaration. Public roots additionally retain an entry. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  scalarRange : row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true
  keyOwner : row.key.declaration = signature.id
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

structure ObservedRoot (fixture : CompiledFixture) (signature : ProgramFunctionSignature) extends ObservedRow fixture signature where
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) (arguments : List TypeSystem.Ty) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id ∧ row.key.arguments = arguments)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨scalarRange⟩ ← observed (row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true) "generic complete raw range"
    let ⟨keyOwner⟩ ← observed (row.key.declaration = signature.id) "generic row key owner"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      return {
        row := row
        member := List.mem_of_find?_eq_some found
        sourceOwner := sourceOwner
        scalarRange := scalarRange
        keyOwner := keyOwner
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
        }
    | _ => throw (IO.userError "reuse unique global slot")


def observeRootRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) : IO (ObservedRoot fixture signature) := do
  let row ← observeRow fixture signature []
  match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.row.key)) with
  | none => throw (IO.userError "public root entry missing")
  | some entry =>
    let ⟨entryKey⟩ ← observed (entry.key = row.row.key) "public root entry key"
    return {toObservedRow := row, entry, entryMember := List.mem_of_find?_eq_some entryFound, entryKey}

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

theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    intro parameter replacement member
    have scalar := of_decide_eq_true (List.all_eq_true.mp observed.scalarRange (parameter, replacement) member)
    rcases scalar with rfl | rfl
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by rw [RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]; exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

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

def seed : Core.Word := Core.Word.ofNatModulo 11

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 102400
  inputValidationFuel := 1024
  outputValidationFuel := 1024 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its function handle is obtained from the actual public export. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 102400 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed] runOptions (.ok (.succeeded completion))
  handle : SourceCorePublicValues.Handle
  returned : completion.value = .function handle
  handleType : handle.sourceType = closureType .word

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 102400 with
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
          if handleType : handle.sourceType = closureType .word then
            return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
              checkpoint, started, completion, result ▸ executed.property, handle, returned, handleType⟩
          else throw (IO.userError "initial public handle type")
        | _ => throw (IO.userError "initial function export missing")

structure SelectedFactoryShape (function : CheckedFunction) (type : TypeSystem.Ty) where
  binder : TypedBinder
  read : Read function.typedBody binder type
  value : CallNode function.typedBody type
  statement : StatementNode
  expression : TypedNode function.typedBody (closureType type)
  outerReturn : StatementNode
  requirement : RequirementId
  requirements : value.node.requirements = [requirement]
  form : value.node.form = .unary .bitNot read.node.id
  inputs : function.typedBody.inputs = [binder]
  binderScheme : binder.scheme = .mono type
  binderRequirements : binder.schemeRequirements = []
  roots : function.typedBody.roots = [.statement outerReturn.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some value.node.id)
  statementType : statement.type = type
  lambda : expression.node.form = .lambda [] type [statement.id]
  outerFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerForm : outerReturn.form = .returnStmt (some expression.node.id)
  outerType : outerReturn.type = closureType type

def SelectedFactoryShape.nodeList {function type} (shape : SelectedFactoryShape function type) : List Node :=
  [.expression shape.read.node, .expression shape.value.node, .statement shape.statement,
   .expression shape.expression.node, .statement shape.outerReturn]

def observeSelectedFactory (function : CheckedFunction) (type : TypeSystem.Ty) : IO (SelectedFactoryShape function type) := do
  let [binder] := function.typedBody.inputs | throw (IO.userError "selected factory input")
  let [.expression readNode, .expression node, .statement statement, .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "selected factory five nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody binder readNode type
  let value ← observeCallNode function.typedBody node type
  let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType type)
  let [requirement] := value.node.requirements | throw (IO.userError "selected factory requirement")
  let ⟨requirements⟩ ← observed (value.node.requirements = [requirement]) "selected factory requirements"
  let ⟨form⟩ ← observed (value.node.form = .unary .bitNot read.node.id) "selected factory form"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [binder]) "selected factory inputs"
  let ⟨binderScheme⟩ ← observed (binder.scheme = .mono type) "selected factory binderScheme"
  let ⟨binderRequirements⟩ ← observed (binder.schemeRequirements = []) "selected factory binderRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "selected factory roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "selected factory statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some value.node.id)) "selected factory statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "selected factory statementType"
  let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] type [statement.id]) "selected factory lambda"
  let ⟨outerFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "selected factory outerFound"
  let ⟨outerForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.node.id)) "selected factory outerForm"
  let ⟨outerType⟩ ← observed (outerReturn.type = closureType type) "selected factory outerType"
  return {binder, read, value, statement, expression, outerReturn, requirement, requirements, form, inputs, binderScheme, binderRequirements, roots, statementFound, statementForm, statementType, lambda, outerFound, outerForm, outerType}

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  makeWordRow : ObservedRow fixture fixture.makeSignature
  makeBoolRow : ObservedRow fixture fixture.makeSignature
  useWordRow : ObservedRoot fixture fixture.useWordSignature
  useBoolRow : ObservedRoot fixture fixture.useBoolSignature
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  makeWordShape : SelectedFactoryShape makeWordRow.row.function .word
  makeBoolShape : SelectedFactoryShape makeBoolRow.row.function .bool
  useWordShape : UseShape useWordRow.row.function fixture.useWordSignature .word
  useBoolShape : UseShape useBoolRow.row.function fixture.useBoolSignature .bool
  wordInputScheme : wordShape.body.binder.scheme = .mono (.word)
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = closureType .word
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolInputScheme : boolShape.body.binder.scheme = .mono (.bool)
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  boolResultType : boolRow.row.function.inferredBodyType = closureType .bool
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  makeWordInputScheme : makeWordShape.binder.scheme = .mono (.word)
  makeWordNodes : makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList
  makeWordResultType : makeWordRow.row.function.inferredBodyType = closureType .word
  makeWordKey : makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩
  makeBoolInputScheme : makeBoolShape.binder.scheme = .mono (.bool)
  makeBoolNodes : makeBoolRow.row.function.typedBody.nodes = makeBoolShape.nodeList
  makeBoolResultType : makeBoolRow.row.function.inferredBodyType = closureType .bool
  makeBoolKey : makeBoolRow.row.key = ⟨fixture.makeSignature.id, [.bool]⟩
  useWordInputScheme : useWordShape.body.binder.scheme = .mono (closureType .word)
  useWordNodes : useWordRow.row.function.typedBody.nodes = useWordShape.nodeList
  useWordResultType : useWordRow.row.function.inferredBodyType = .word
  useWordKey : useWordRow.row.key = ⟨fixture.useWordSignature.id, []⟩
  useBoolInputScheme : useBoolShape.body.binder.scheme = .mono (closureType .bool)
  useBoolNodes : useBoolRow.row.function.typedBody.nodes = useBoolShape.nodeList
  useBoolResultType : useBoolRow.row.function.inferredBodyType = .bool
  useBoolKey : useBoolRow.row.key = ⟨fixture.useBoolSignature.id, []⟩
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row
  ordinarySlotsDistinct : [wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, useWordRow.index, useBoolRow.index].Nodup
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 8
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let makeWordRow ← observeRow fixture fixture.makeSignature [.word]
  let makeBoolRow ← observeRow fixture fixture.makeSignature [.bool]
  let useWordRow ← observeRootRow fixture fixture.useWordSignature
  let useBoolRow ← observeRootRow fixture fixture.useBoolSignature
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  let makeWordShape ← observeSelectedFactory makeWordRow.row.function .word
  let makeBoolShape ← observeSelectedFactory makeBoolRow.row.function .bool
  let useWordShape ← observeUse useWordRow.row.function fixture.useWordSignature .word
  let useBoolShape ← observeUse useBoolRow.row.function fixture.useBoolSignature .bool
  let ⟨wordInputScheme⟩ ← observed (wordShape.body.binder.scheme = .mono (.word)) "actual method closure wordInputScheme"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "actual method closure wordNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = closureType .word) "actual method closure wordResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "actual method closure wordKey"
  let ⟨boolInputScheme⟩ ← observed (boolShape.body.binder.scheme = .mono (.bool)) "actual method closure boolInputScheme"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "actual method closure boolNodes"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = closureType .bool) "actual method closure boolResultType"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "actual method closure boolKey"
  let ⟨makeWordInputScheme⟩ ← observed (makeWordShape.binder.scheme = .mono (.word)) "actual method closure makeWordInputScheme"
  let ⟨makeWordNodes⟩ ← observed (makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList) "actual method closure makeWordNodes"
  let ⟨makeWordResultType⟩ ← observed (makeWordRow.row.function.inferredBodyType = closureType .word) "actual method closure makeWordResultType"
  let ⟨makeWordKey⟩ ← observed (makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩) "actual method closure makeWordKey"
  let ⟨makeBoolInputScheme⟩ ← observed (makeBoolShape.binder.scheme = .mono (.bool)) "actual method closure makeBoolInputScheme"
  let ⟨makeBoolNodes⟩ ← observed (makeBoolRow.row.function.typedBody.nodes = makeBoolShape.nodeList) "actual method closure makeBoolNodes"
  let ⟨makeBoolResultType⟩ ← observed (makeBoolRow.row.function.inferredBodyType = closureType .bool) "actual method closure makeBoolResultType"
  let ⟨makeBoolKey⟩ ← observed (makeBoolRow.row.key = ⟨fixture.makeSignature.id, [.bool]⟩) "actual method closure makeBoolKey"
  let ⟨useWordInputScheme⟩ ← observed (useWordShape.body.binder.scheme = .mono (closureType .word)) "actual method closure useWordInputScheme"
  let ⟨useWordNodes⟩ ← observed (useWordRow.row.function.typedBody.nodes = useWordShape.nodeList) "actual method closure useWordNodes"
  let ⟨useWordResultType⟩ ← observed (useWordRow.row.function.inferredBodyType = .word) "actual method closure useWordResultType"
  let ⟨useWordKey⟩ ← observed (useWordRow.row.key = ⟨fixture.useWordSignature.id, []⟩) "actual method closure useWordKey"
  let ⟨useBoolInputScheme⟩ ← observed (useBoolShape.body.binder.scheme = .mono (closureType .bool)) "actual method closure useBoolInputScheme"
  let ⟨useBoolNodes⟩ ← observed (useBoolRow.row.function.typedBody.nodes = useBoolShape.nodeList) "actual method closure useBoolNodes"
  let ⟨useBoolResultType⟩ ← observed (useBoolRow.row.function.inferredBodyType = .bool) "actual method closure useBoolResultType"
  let ⟨useBoolKey⟩ ← observed (useBoolRow.row.key = ⟨fixture.useBoolSignature.id, []⟩) "actual method closure useBoolKey"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row) "actual method closure wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row) "actual method closure boolInstantiation"
  let ⟨ordinarySlotsDistinct⟩ ← observed ([wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, useWordRow.index, useBoolRow.index].Nodup) "actual method closure ordinarySlotsDistinct"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 8) "actual method closure globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]) "actual method closure entryKeys"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual method closure noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual method closure profile"
  return {wordRow, boolRow, makeWordRow, makeBoolRow, useWordRow, useBoolRow, wordShape, boolShape, makeWordShape, makeBoolShape, useWordShape, useBoolShape, wordInputScheme, wordNodes, wordResultType, wordKey, boolInputScheme, boolNodes, boolResultType, boolKey, makeWordInputScheme, makeWordNodes, makeWordResultType, makeWordKey, makeBoolInputScheme, makeBoolNodes, makeBoolResultType, makeBoolKey, useWordInputScheme, useWordNodes, useWordResultType, useWordKey, useBoolInputScheme, useBoolNodes, useBoolResultType, useBoolKey, wordInstantiation, boolInstantiation, ordinarySlotsDistinct, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreMethodClosure
