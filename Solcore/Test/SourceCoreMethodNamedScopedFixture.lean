import Solcore.Test.SourceCoreMethodNamedScopedSource
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
namespace Tests.SourceCoreMethodNamedScoped
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
  started : session.start observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions (.ok (.succeeded completion))
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
    match started : session.start observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] runOptions
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

structure SelectedRelayShape (function : CheckedFunction) (type : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  localBinder : TypedBinder
  firstRead : Read function.typedBody first type
  call : MethodUnary function.typedBody type firstRead.node.id
  initialized : StatementNode
  conditionRead : Read function.typedBody flag .bool
  loopSecondRead : Read function.typedBody second type
  loopCall : MethodUnary function.typedBody type loopSecondRead.node.id
  assignment : StatementNode
  resolution : AssignmentResolution
  stop : TypedNode function.typedBody .bool
  flagAssignment : StatementNode
  flagResolution : AssignmentResolution
  loop : StatementNode
  finalRead : Read function.typedBody localBinder type
  finalCall : MethodUnary function.typedBody type finalRead.node.id
  statement : StatementNode
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono type
  secondScheme : second.scheme = .mono type
  flagScheme : flag.scheme = .mono .bool
  localScheme : localBinder.scheme = .mono type
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  flagRequirements : flag.schemeRequirements = []
  localRequirements : localBinder.schemeRequirements = []
  firstClosed : type.freeVariables = []
  flagOwner : flag.id.owner = function.typedBody.owner
  localOwner : localBinder.id.owner = function.typedBody.owner
  localOrdinary : localBinder.comptime = false
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  localFirst : localBinder.id ≠ first.id
  localSecond : localBinder.id ≠ second.id
  localFlag : localBinder.id ≠ flag.id
  roots : function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]
  initializedFound : function.typedBody.lookupStatement? initialized.id = some initialized
  initializedForm : initialized.form = .letDecl localBinder (some call.value.node.id)
  initializedType : initialized.type = .unit
  assignmentFound : function.typedBody.lookupStatement? assignment.id = some assignment
  assignmentForm : assignment.form = .assignValue resolution .equal loopCall.value.node.id
  assignmentType : assignment.type = .unit
  targetRoot : resolution.target.root = localBinder.id
  targetType : resolution.target.type = type
  targetBare : resolution.target.projections = []
  assignmentRequirements : resolution.requirements = []
  stopForm : stop.node.form = .reference "false" (.builtinBoolean false)
  flagAssignmentFound : function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment
  flagAssignmentForm : flagAssignment.form = .assignValue flagResolution .equal stop.node.id
  flagAssignmentType : flagAssignment.type = .unit
  flagTargetRoot : flagResolution.target.root = flag.id
  flagTargetType : flagResolution.target.type = .bool
  flagTargetBare : flagResolution.target.projections = []
  flagAssignmentRequirements : flagResolution.requirements = []
  loopFound : function.typedBody.lookupStatement? loop.id = some loop
  loopForm : loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]
  loopType : loop.type = .unit
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some finalCall.value.node.id)
  statementType : statement.type = type

def SelectedRelayShape.body {function type}
    (shape : SelectedRelayShape function type) :=
  [shape.initialized.id, shape.loop.id, shape.statement.id]

def SelectedRelayShape.nodeList {function type}
    (shape : SelectedRelayShape function type) : List Node :=
  [.expression shape.firstRead.node, .expression shape.call.value.node, .statement shape.initialized,
   .expression shape.conditionRead.node, .expression shape.loopSecondRead.node,
   .expression shape.loopCall.value.node, .statement shape.assignment,
   .expression shape.stop.node, .statement shape.flagAssignment, .statement shape.loop,
   .expression shape.finalRead.node, .expression shape.finalCall.value.node, .statement shape.statement]


def observeSelectedRelay (function : CheckedFunction) (type : TypeSystem.Ty) :
    IO (SelectedRelayShape function type) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "relay inputs")
  let [.expression firstNode, .expression initialValue, .statement initialized,
      .expression conditionNode, .expression loopSecondNode, .expression loopValue, .statement assignment,
      .expression stopNode, .statement flagAssignment, .statement loop,
      .expression finalNode, .expression finalValue, .statement statement] := function.typedBody.nodes
      | throw (IO.userError "relay thirteen nodes")
  let .letDecl localBinder _ := initialized.form | throw (IO.userError "relay initialized binder")
  let .assignValue resolution .equal _ := assignment.form | throw (IO.userError "relay saved assignment")
  let .assignValue flagResolution .equal _ := flagAssignment.form | throw (IO.userError "relay flag assignment")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first firstNode type
  let call ← observeUnary function.typedBody type firstRead.node.id initialValue
  let conditionRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag conditionNode .bool
  let loopSecondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second loopSecondNode type
  let loopCall ← observeUnary function.typedBody type loopSecondRead.node.id loopValue
  let stop ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody stopNode .bool
  let finalRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody localBinder finalNode type
  let finalCall ← observeUnary function.typedBody type finalRead.node.id finalValue
  let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "relay noTemplates"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "relay inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono type) "relay firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono type) "relay secondScheme"
  let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "relay flagScheme"
  let ⟨localScheme⟩ ← observed (localBinder.scheme = .mono type) "relay localScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "relay firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "relay secondRequirements"
  let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "relay flagRequirements"
  let ⟨localRequirements⟩ ← observed (localBinder.schemeRequirements = []) "relay localRequirements"
  let ⟨firstClosed⟩ ← observed (type.freeVariables = []) "relay firstClosed"
  let ⟨flagOwner⟩ ← observed (flag.id.owner = function.typedBody.owner) "relay flagOwner"
  let ⟨localOwner⟩ ← observed (localBinder.id.owner = function.typedBody.owner) "relay localOwner"
  let ⟨localOrdinary⟩ ← observed (localBinder.comptime = false) "relay localOrdinary"
  let ⟨different⟩ ← observed (second.id ≠ first.id) "relay different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "relay flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "relay flagSecond"
  let ⟨localFirst⟩ ← observed (localBinder.id ≠ first.id) "relay localFirst"
  let ⟨localSecond⟩ ← observed (localBinder.id ≠ second.id) "relay localSecond"
  let ⟨localFlag⟩ ← observed (localBinder.id ≠ flag.id) "relay localFlag"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement initialized.id, .statement loop.id, .statement statement.id]) "relay roots"
  let ⟨initializedFound⟩ ← observed (function.typedBody.lookupStatement? initialized.id = some initialized) "relay initializedFound"
  let ⟨initializedForm⟩ ← observed (initialized.form = .letDecl localBinder (some call.value.node.id)) "relay initializedForm"
  let ⟨initializedType⟩ ← observed (initialized.type = .unit) "relay initializedType"
  let ⟨assignmentFound⟩ ← observed (function.typedBody.lookupStatement? assignment.id = some assignment) "relay assignmentFound"
  let ⟨assignmentForm⟩ ← observed (assignment.form = .assignValue resolution .equal loopCall.value.node.id) "relay assignmentForm"
  let ⟨assignmentType⟩ ← observed (assignment.type = .unit) "relay assignmentType"
  let ⟨targetRoot⟩ ← observed (resolution.target.root = localBinder.id) "relay targetRoot"
  let ⟨targetType⟩ ← observed (resolution.target.type = type) "relay targetType"
  let ⟨targetBare⟩ ← observed (resolution.target.projections = []) "relay targetBare"
  let ⟨assignmentRequirements⟩ ← observed (resolution.requirements = []) "relay assignmentRequirements"
  let ⟨stopForm⟩ ← observed (stop.node.form = .reference "false" (.builtinBoolean false)) "relay stopForm"
  let ⟨flagAssignmentFound⟩ ← observed (function.typedBody.lookupStatement? flagAssignment.id = some flagAssignment) "relay flagAssignmentFound"
  let ⟨flagAssignmentForm⟩ ← observed (flagAssignment.form = .assignValue flagResolution .equal stop.node.id) "relay flagAssignmentForm"
  let ⟨flagAssignmentType⟩ ← observed (flagAssignment.type = .unit) "relay flagAssignmentType"
  let ⟨flagTargetRoot⟩ ← observed (flagResolution.target.root = flag.id) "relay flagTargetRoot"
  let ⟨flagTargetType⟩ ← observed (flagResolution.target.type = .bool) "relay flagTargetType"
  let ⟨flagTargetBare⟩ ← observed (flagResolution.target.projections = []) "relay flagTargetBare"
  let ⟨flagAssignmentRequirements⟩ ← observed (flagResolution.requirements = []) "relay flagAssignmentRequirements"
  let ⟨loopFound⟩ ← observed (function.typedBody.lookupStatement? loop.id = some loop) "relay loopFound"
  let ⟨loopForm⟩ ← observed (loop.form = .whileLoop conditionRead.node.id [assignment.id, flagAssignment.id]) "relay loopForm"
  let ⟨loopType⟩ ← observed (loop.type = .unit) "relay loopType"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "relay statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some finalCall.value.node.id)) "relay statementForm"
  let ⟨statementType⟩ ← observed (statement.type = type) "relay statementType"
  return {first, second, flag, localBinder, firstRead, call, initialized, conditionRead, loopSecondRead, loopCall, assignment, resolution, stop, flagAssignment, flagResolution, loop, finalRead, finalCall, statement, noTemplates, inputs, firstScheme, secondScheme, flagScheme, localScheme, firstRequirements, secondRequirements, flagRequirements, localRequirements, firstClosed, flagOwner, localOwner, localOrdinary, different, flagFirst, flagSecond, localFirst, localSecond, localFlag, roots, initializedFound, initializedForm, initializedType, assignmentFound, assignmentForm, assignmentType, targetRoot, targetType, targetBare, assignmentRequirements, stopForm, flagAssignmentFound, flagAssignmentForm, flagAssignmentType, flagTargetRoot, flagTargetType, flagTargetBare, flagAssignmentRequirements, loopFound, loopForm, loopType, statementFound, statementForm, statementType}
structure SelectedFactoryShape (function : CheckedFunction) (generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) where
  first : TypedBinder
  second : TypedBinder
  flag : TypedBinder
  different : second.id ≠ first.id
  flagFirst : flag.id ≠ first.id
  flagSecond : flag.id ≠ second.id
  firstRead : Read function.typedBody first type
  secondRead : Read function.typedBody second type
  flagRead : Read function.typedBody flag .bool
  call : RelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id trait
  statement : StatementNode
  solved : SolvedRequirement
  solvedMember : solved ∈ function.solvedRequirements
  solvedId : solved.id = call.requirement
  solvedPredicate : solved.predicate = predicate trait type
  noTemplates : sourceLocalSchemeTemplateIds function.typedBody = []
  inputs : function.typedBody.inputs = [first, second, flag]
  firstScheme : first.scheme = .mono type
  secondScheme : second.scheme = .mono type
  flagScheme : flag.scheme = .mono .bool
  flagRequirements : flag.schemeRequirements = []
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  expression : TypedNode function.typedBody (closureType type)
  outerReturn : StatementNode
  roots : function.typedBody.roots = [.statement outerReturn.id]
  lambda : expression.node.form = .lambda [] type [statement.id]
  outerReturnFound : function.typedBody.lookupStatement? outerReturn.id = some outerReturn
  outerReturnForm : outerReturn.form = .returnStmt (some expression.node.id)
  outerReturnType : outerReturn.type = closureType type
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = type

def SelectedFactoryShape.nodeList {function generic parameter type trait}
    (shape : SelectedFactoryShape function generic parameter type trait) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.flagRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement, .expression shape.expression.node, .statement shape.outerReturn]

def observeSelectedFactory (function : CheckedFunction) (generic : ProgramFunctionSignature)
    (parameter : TypeSystem.TypeParameterId) (type : TypeSystem.Ty) (trait : ProgramTraitId) :
    IO (SelectedFactoryShape function generic parameter type trait) := do
  let [first, second, flag] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression readFlag, .expression callee, .expression value, .statement statement, .expression lambdaNode, .statement outerReturn] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst type
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond type
  let flagRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody flag readFlag .bool
  let call ← observeRelayCall function.typedBody generic parameter type firstRead.node.id secondRead.node.id flagRead.node.id callee value trait
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  let ⟨flagFirst⟩ ← observed (flag.id ≠ first.id) "flagFirst"
  let ⟨flagSecond⟩ ← observed (flag.id ≠ second.id) "flagSecond"
  match rows : function.solvedRequirements with
  | [solved] =>
    let solvedMember : solved ∈ function.solvedRequirements := by simp [rows]
    let ⟨solvedId⟩ ← observed (solved.id = call.requirement) "call solved identity"
    let ⟨solvedPredicate⟩ ← observed (solved.predicate = predicate trait type) "call solved predicate"
    let ⟨noTemplates⟩ ← observed (sourceLocalSchemeTemplateIds function.typedBody = []) "no templates"
    let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second, flag]) "generic root inputs"
    let ⟨firstScheme⟩ ← observed (first.scheme = .mono type) "generic root firstScheme"
    let ⟨secondScheme⟩ ← observed (second.scheme = .mono type) "generic root secondScheme"
    let ⟨flagScheme⟩ ← observed (flag.scheme = .mono .bool) "flagScheme"
    let ⟨flagRequirements⟩ ← observed (flag.schemeRequirements = []) "flagRequirements"
    let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
    let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
    let expression ← Tests.SourceCoreOperatorCalls.observeNode function.typedBody lambdaNode (closureType type)
    let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement outerReturn.id]) "factory roots"
    let ⟨lambda⟩ ← observed (expression.node.form = .lambda [] type [statement.id]) "factory lambda"
    let ⟨outerReturnFound⟩ ← observed (function.typedBody.lookupStatement? outerReturn.id = some outerReturn) "outerReturnFound"
    let ⟨outerReturnForm⟩ ← observed (outerReturn.form = .returnStmt (some expression.node.id)) "outerReturnForm"
    let ⟨outerReturnType⟩ ← observed (outerReturn.type = closureType type) "outerReturnType"
    let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
    let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
    let ⟨statementType⟩ ← observed (statement.type = type) "generic root statementType"
    return {expression, outerReturn, lambda, outerReturnFound, outerReturnForm, outerReturnType, flag, flagRead, flagFirst, flagSecond, flagScheme, flagRequirements, first, second, firstRead, secondRead, call, statement, different, solved, solvedMember, solvedId, solvedPredicate, noTemplates, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}
  | _ => throw (IO.userError "call ledger")


structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  makeWordRow : ObservedRow fixture fixture.makeSignature
  makeBoolRow : ObservedRow fixture fixture.makeSignature
  relayWordRow : ObservedRow fixture fixture.relaySignature
  relayBoolRow : ObservedRow fixture fixture.relaySignature
  useWordRow : ObservedRoot fixture fixture.useWordSignature
  useBoolRow : ObservedRoot fixture fixture.useBoolSignature
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  makeWordShape : SelectedFactoryShape makeWordRow.row.function fixture.relaySignature fixture.relayParameter .word (.declaration fixture.trait.id)
  makeBoolShape : SelectedFactoryShape makeBoolRow.row.function fixture.relaySignature fixture.relayParameter .bool (.declaration fixture.trait.id)
  relayWordShape : SelectedRelayShape relayWordRow.row.function .word
  relayBoolShape : SelectedRelayShape relayBoolRow.row.function .bool
  useWordShape : UseShape useWordRow.row.function fixture.useWordSignature .word
  useBoolShape : UseShape useBoolRow.row.function fixture.useBoolSignature .bool
  wordInputScheme : wordShape.first.scheme = .mono (.word)
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = closureType .word
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolInputScheme : boolShape.first.scheme = .mono (.bool)
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  boolResultType : boolRow.row.function.inferredBodyType = closureType .bool
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  makeWordInputScheme : makeWordShape.first.scheme = .mono (.word)
  makeWordNodes : makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList
  makeWordResultType : makeWordRow.row.function.inferredBodyType = closureType .word
  makeWordKey : makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩
  makeBoolInputScheme : makeBoolShape.first.scheme = .mono (.bool)
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
  relayWordNodes : relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList
  relayWordResultType : relayWordRow.row.function.inferredBodyType = .word
  relayWordKey : relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word]⟩
  makeWordRelayInstantiation : makeWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row
  relayBoolNodes : relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList
  relayBoolResultType : relayBoolRow.row.function.inferredBodyType = .bool
  relayBoolKey : relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool]⟩
  makeBoolRelayInstantiation : makeBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row
  ordinarySlotsDistinct : [wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, relayWordRow.index, relayBoolRow.index, useWordRow.index, useBoolRow.index].Nodup
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 10
  entryKeys : fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let makeWordRow ← observeRow fixture fixture.makeSignature [.word]
  let makeBoolRow ← observeRow fixture fixture.makeSignature [.bool]
  let relayWordRow ← observeRow fixture fixture.relaySignature [.word]
  let relayBoolRow ← observeRow fixture fixture.relaySignature [.bool]
  let useWordRow ← observeRootRow fixture fixture.useWordSignature
  let useBoolRow ← observeRootRow fixture fixture.useBoolSignature
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.makeSignature fixture.parameter .word (.declaration fixture.trait.id)
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.makeSignature fixture.parameter .bool (.declaration fixture.trait.id)
  let makeWordShape ← observeSelectedFactory makeWordRow.row.function fixture.relaySignature fixture.relayParameter .word (.declaration fixture.trait.id)
  let makeBoolShape ← observeSelectedFactory makeBoolRow.row.function fixture.relaySignature fixture.relayParameter .bool (.declaration fixture.trait.id)
  let relayWordShape ← observeSelectedRelay relayWordRow.row.function .word
  let relayBoolShape ← observeSelectedRelay relayBoolRow.row.function .bool
  let useWordShape ← observeUse useWordRow.row.function fixture.useWordSignature .word
  let useBoolShape ← observeUse useBoolRow.row.function fixture.useBoolSignature .bool
  let ⟨wordInputScheme⟩ ← observed (wordShape.first.scheme = .mono (.word)) "actual method closure wordInputScheme"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "actual method closure wordNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = closureType .word) "actual method closure wordResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "actual method closure wordKey"
  let ⟨boolInputScheme⟩ ← observed (boolShape.first.scheme = .mono (.bool)) "actual method closure boolInputScheme"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "actual method closure boolNodes"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = closureType .bool) "actual method closure boolResultType"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "actual method closure boolKey"
  let ⟨makeWordInputScheme⟩ ← observed (makeWordShape.first.scheme = .mono (.word)) "actual method closure makeWordInputScheme"
  let ⟨makeWordNodes⟩ ← observed (makeWordRow.row.function.typedBody.nodes = makeWordShape.nodeList) "actual method closure makeWordNodes"
  let ⟨makeWordResultType⟩ ← observed (makeWordRow.row.function.inferredBodyType = closureType .word) "actual method closure makeWordResultType"
  let ⟨makeWordKey⟩ ← observed (makeWordRow.row.key = ⟨fixture.makeSignature.id, [.word]⟩) "actual method closure makeWordKey"
  let ⟨makeBoolInputScheme⟩ ← observed (makeBoolShape.first.scheme = .mono (.bool)) "actual method closure makeBoolInputScheme"
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
  let ⟨relayWordNodes⟩ ← observed (relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList) "relayWord nodes"
  let ⟨relayWordResultType⟩ ← observed (relayWordRow.row.function.inferredBodyType = .word) "relayWord result"
  let ⟨relayWordKey⟩ ← observed (relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word]⟩) "relayWord key"
  let ⟨makeWordRelayInstantiation⟩ ← observed (makeWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row) "makeWordRelayInstantiation"
  let ⟨relayBoolNodes⟩ ← observed (relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList) "relayBool nodes"
  let ⟨relayBoolResultType⟩ ← observed (relayBoolRow.row.function.inferredBodyType = .bool) "relayBool result"
  let ⟨relayBoolKey⟩ ← observed (relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool]⟩) "relayBool key"
  let ⟨makeBoolRelayInstantiation⟩ ← observed (makeBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row) "makeBoolRelayInstantiation"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeWordRow.row) "actual method closure wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation makeBoolRow.row) "actual method closure boolInstantiation"
  let ⟨ordinarySlotsDistinct⟩ ← observed ([wordRow.index, boolRow.index, makeWordRow.index, makeBoolRow.index, relayWordRow.index, relayBoolRow.index, useWordRow.index, useBoolRow.index].Nodup) "actual method closure ordinarySlotsDistinct"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 10) "actual method closure globalsLength"
  let ⟨entryKeys⟩ ← observed (fixture.recipe.compiled.indexed.entries.map (·.key) = [wordRow.row.key, boolRow.row.key, useWordRow.row.key, useBoolRow.row.key]) "actual method closure entryKeys"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "actual method closure noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "actual method closure profile"
  return {relayWordRow, relayBoolRow, relayWordShape, relayBoolShape, relayWordNodes, relayWordResultType, relayWordKey, makeWordRelayInstantiation, relayBoolNodes, relayBoolResultType, relayBoolKey, makeBoolRelayInstantiation, wordRow, boolRow, makeWordRow, makeBoolRow, useWordRow, useBoolRow, wordShape, boolShape, makeWordShape, makeBoolShape, useWordShape, useBoolShape, wordInputScheme, wordNodes, wordResultType, wordKey, boolInputScheme, boolNodes, boolResultType, boolKey, makeWordInputScheme, makeWordNodes, makeWordResultType, makeWordKey, makeBoolInputScheme, makeBoolNodes, makeBoolResultType, makeBoolKey, useWordInputScheme, useWordNodes, useWordResultType, useWordKey, useBoolInputScheme, useBoolNodes, useBoolResultType, useBoolKey, wordInstantiation, boolInstantiation, ordinarySlotsDistinct, globalsLength, entryKeys, noLocals, profile}

end Tests.SourceCoreMethodNamedScoped
