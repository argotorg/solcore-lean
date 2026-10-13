import Solcore.Test.SourceCoreEvidenceScopedSource
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
namespace Tests.SourceCoreEvidenceScoped
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
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id]
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

structure SelectedShape (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  read : Read function.typedBody first firstType
  statement : StatementNode
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = firstType
  resultType : function.inferredBodyType = firstType

def SelectedShape.nodeList {function firstType secondType} (shape : SelectedShape function firstType secondType) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

def observeSelected (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) : IO (SelectedShape function firstType secondType) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "generic selected inputs")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "generic selected nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first node firstType
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "selected inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "selected firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "selected secondScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "selected firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "selected secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "selected roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "selected statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "selected statementForm"
  let ⟨statementType⟩ ← observed (statement.type = firstType) "selected statementType"
  let ⟨resultType⟩ ← observed (function.inferredBodyType = firstType) "selected resultType"
  return {first, second, read, statement, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType, resultType}

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  relayWordRow : ObservedRow fixture fixture.relaySignature
  relayBoolRow : ObservedRow fixture fixture.relaySignature
  chooseWordRow : ObservedRow fixture fixture.chooseSignature
  chooseBoolRow : ObservedRow fixture fixture.chooseSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 6
  indexCoverage : (List.range 6).all (fun index => decide (index ∈ [wordRow.index, boolRow.index, relayWordRow.index, relayBoolRow.index, chooseWordRow.index, chooseBoolRow.index])) = true
  wordBool : wordRow.index ≠ boolRow.index
  wordRelayWord : wordRow.index ≠ relayWordRow.index
  wordRelayBool : wordRow.index ≠ relayBoolRow.index
  wordChooseWord : wordRow.index ≠ chooseWordRow.index
  wordChooseBool : wordRow.index ≠ chooseBoolRow.index
  boolRelayWord : boolRow.index ≠ relayWordRow.index
  boolRelayBool : boolRow.index ≠ relayBoolRow.index
  boolChooseWord : boolRow.index ≠ chooseWordRow.index
  boolChooseBool : boolRow.index ≠ chooseBoolRow.index
  relayWordRelayBool : relayWordRow.index ≠ relayBoolRow.index
  relayWordChooseWord : relayWordRow.index ≠ chooseWordRow.index
  relayWordChooseBool : relayWordRow.index ≠ chooseBoolRow.index
  relayBoolChooseWord : relayBoolRow.index ≠ chooseWordRow.index
  relayBoolChooseBool : relayBoolRow.index ≠ chooseBoolRow.index
  chooseWordChooseBool : chooseWordRow.index ≠ chooseBoolRow.index
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.relaySignature fixture.relayFirstParameter fixture.relaySecondParameter .word .bool fixture.trait
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.relaySignature fixture.relayFirstParameter fixture.relaySecondParameter .bool .word fixture.trait
  relayWordShape : RelayShape relayWordRow.row.function fixture.relaySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool fixture.trait
  relayBoolShape : RelayShape relayBoolRow.row.function fixture.relaySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word fixture.trait
  chooseWordShape : SelectedShape chooseWordRow.row.function .word .bool
  chooseBoolShape : SelectedShape chooseBoolRow.row.function .bool .word
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  relayWordNodes : relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList
  relayBoolNodes : relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList
  chooseWordNodes : chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList
  chooseBoolNodes : chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = .word
  boolResultType : boolRow.row.function.inferredBodyType = .bool
  relayWordResultType : relayWordRow.row.function.inferredBodyType = .word
  relayBoolResultType : relayBoolRow.row.function.inferredBodyType = .bool
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  relayWordKey : relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word, .bool]⟩
  relayBoolKey : relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool, .word]⟩
  chooseWordKey : chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩
  chooseBoolKey : chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩
  wordParameters : wordRow.row.parameterSubstitution = []
  boolParameters : boolRow.row.parameterSubstitution = []
  relayWordParameters : relayWordRow.row.parameterSubstitution = [(fixture.relayFirstParameter, .word), (fixture.relaySecondParameter, .bool)]
  relayBoolParameters : relayBoolRow.row.parameterSubstitution = [(fixture.relayFirstParameter, .bool), (fixture.relaySecondParameter, .word)]
  chooseWordParameters : chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]
  chooseBoolParameters : chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row
  relayWordInstantiation : relayWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row
  relayBoolInstantiation : relayBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row
  relayWordLoopInstantiation : relayWordShape.loopCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row
  relayBoolLoopInstantiation : relayBoolShape.loopCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row
  relayWordFinalInstantiation : relayWordShape.finalCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row
  relayBoolFinalInstantiation : relayBoolShape.finalCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let relayWordRow ← observeRow fixture fixture.relaySignature [.word, .bool]
  let relayBoolRow ← observeRow fixture fixture.relaySignature [.bool, .word]
  let chooseWordRow ← observeRow fixture fixture.chooseSignature [.word, .bool]
  let chooseBoolRow ← observeRow fixture fixture.chooseSignature [.bool, .word]
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.relaySignature fixture.relayFirstParameter fixture.relaySecondParameter .word .bool fixture.trait
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.relaySignature fixture.relayFirstParameter fixture.relaySecondParameter .bool .word fixture.trait
  let relayWordShape ← observeRelay relayWordRow.row.function fixture.relaySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool fixture.trait
  let relayBoolShape ← observeRelay relayBoolRow.row.function fixture.relaySignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word fixture.trait
  let chooseWordShape ← observeSelected chooseWordRow.row.function .word .bool
  let chooseBoolShape ← observeSelected chooseBoolRow.row.function .bool .word
  let ⟨indexCoverage⟩ ← observed ((List.range 6).all (fun index => decide (index ∈ [wordRow.index, boolRow.index, relayWordRow.index, relayBoolRow.index, chooseWordRow.index, chooseBoolRow.index])) = true) "actual six slots coverage"
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 6) "evidence program globalsLength"
  let ⟨wordBool⟩ ← observed (wordRow.index ≠ boolRow.index) "evidence program wordBool"
  let ⟨wordRelayWord⟩ ← observed (wordRow.index ≠ relayWordRow.index) "evidence program wordRelayWord"
  let ⟨wordRelayBool⟩ ← observed (wordRow.index ≠ relayBoolRow.index) "evidence program wordRelayBool"
  let ⟨wordChooseWord⟩ ← observed (wordRow.index ≠ chooseWordRow.index) "evidence program wordChooseWord"
  let ⟨wordChooseBool⟩ ← observed (wordRow.index ≠ chooseBoolRow.index) "evidence program wordChooseBool"
  let ⟨boolRelayWord⟩ ← observed (boolRow.index ≠ relayWordRow.index) "evidence program boolRelayWord"
  let ⟨boolRelayBool⟩ ← observed (boolRow.index ≠ relayBoolRow.index) "evidence program boolRelayBool"
  let ⟨boolChooseWord⟩ ← observed (boolRow.index ≠ chooseWordRow.index) "evidence program boolChooseWord"
  let ⟨boolChooseBool⟩ ← observed (boolRow.index ≠ chooseBoolRow.index) "evidence program boolChooseBool"
  let ⟨relayWordRelayBool⟩ ← observed (relayWordRow.index ≠ relayBoolRow.index) "evidence program relayWordRelayBool"
  let ⟨relayWordChooseWord⟩ ← observed (relayWordRow.index ≠ chooseWordRow.index) "evidence program relayWordChooseWord"
  let ⟨relayWordChooseBool⟩ ← observed (relayWordRow.index ≠ chooseBoolRow.index) "evidence program relayWordChooseBool"
  let ⟨relayBoolChooseWord⟩ ← observed (relayBoolRow.index ≠ chooseWordRow.index) "evidence program relayBoolChooseWord"
  let ⟨relayBoolChooseBool⟩ ← observed (relayBoolRow.index ≠ chooseBoolRow.index) "evidence program relayBoolChooseBool"
  let ⟨chooseWordChooseBool⟩ ← observed (chooseWordRow.index ≠ chooseBoolRow.index) "evidence program chooseWordChooseBool"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "evidence program wordNodes"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "evidence program boolNodes"
  let ⟨relayWordNodes⟩ ← observed (relayWordRow.row.function.typedBody.nodes = relayWordShape.nodeList) "evidence program relayWordNodes"
  let ⟨relayBoolNodes⟩ ← observed (relayBoolRow.row.function.typedBody.nodes = relayBoolShape.nodeList) "evidence program relayBoolNodes"
  let ⟨chooseWordNodes⟩ ← observed (chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList) "evidence program chooseWordNodes"
  let ⟨chooseBoolNodes⟩ ← observed (chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList) "evidence program chooseBoolNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = .word) "evidence program wordResultType"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = .bool) "evidence program boolResultType"
  let ⟨relayWordResultType⟩ ← observed (relayWordRow.row.function.inferredBodyType = .word) "evidence program relayWordResultType"
  let ⟨relayBoolResultType⟩ ← observed (relayBoolRow.row.function.inferredBodyType = .bool) "evidence program relayBoolResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "evidence program wordKey"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "evidence program boolKey"
  let ⟨relayWordKey⟩ ← observed (relayWordRow.row.key = ⟨fixture.relaySignature.id, [.word, .bool]⟩) "evidence program relayWordKey"
  let ⟨relayBoolKey⟩ ← observed (relayBoolRow.row.key = ⟨fixture.relaySignature.id, [.bool, .word]⟩) "evidence program relayBoolKey"
  let ⟨chooseWordKey⟩ ← observed (chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩) "evidence program chooseWordKey"
  let ⟨chooseBoolKey⟩ ← observed (chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩) "evidence program chooseBoolKey"
  let ⟨wordParameters⟩ ← observed (wordRow.row.parameterSubstitution = []) "evidence program wordParameters"
  let ⟨boolParameters⟩ ← observed (boolRow.row.parameterSubstitution = []) "evidence program boolParameters"
  let ⟨relayWordParameters⟩ ← observed (relayWordRow.row.parameterSubstitution = [(fixture.relayFirstParameter, .word), (fixture.relaySecondParameter, .bool)]) "evidence program relayWordParameters"
  let ⟨relayBoolParameters⟩ ← observed (relayBoolRow.row.parameterSubstitution = [(fixture.relayFirstParameter, .bool), (fixture.relaySecondParameter, .word)]) "evidence program relayBoolParameters"
  let ⟨chooseWordParameters⟩ ← observed (chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]) "evidence program chooseWordParameters"
  let ⟨chooseBoolParameters⟩ ← observed (chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]) "evidence program chooseBoolParameters"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayWordRow.row) "evidence program wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation relayBoolRow.row) "evidence program boolInstantiation"
  let ⟨relayWordInstantiation⟩ ← observed (relayWordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row) "evidence program relayWordInstantiation"
  let ⟨relayBoolInstantiation⟩ ← observed (relayBoolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row) "evidence program relayBoolInstantiation"
  let ⟨relayWordLoopInstantiation⟩ ← observed (relayWordShape.loopCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row) "evidence program relayWordLoopInstantiation"
  let ⟨relayBoolLoopInstantiation⟩ ← observed (relayBoolShape.loopCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row) "evidence program relayBoolLoopInstantiation"
  let ⟨relayWordFinalInstantiation⟩ ← observed (relayWordShape.finalCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row) "evidence program relayWordFinalInstantiation"
  let ⟨relayBoolFinalInstantiation⟩ ← observed (relayBoolShape.finalCall.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row) "evidence program relayBoolFinalInstantiation"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "evidence program noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "evidence program profile"
  return {indexCoverage, wordRow, boolRow, relayWordRow, relayBoolRow, chooseWordRow, chooseBoolRow, globalsLength, wordBool, wordRelayWord, wordRelayBool, wordChooseWord, wordChooseBool, boolRelayWord, boolRelayBool, boolChooseWord, boolChooseBool, relayWordRelayBool, relayWordChooseWord, relayWordChooseBool, relayBoolChooseWord, relayBoolChooseBool, chooseWordChooseBool, wordShape, boolShape, relayWordShape, relayBoolShape, chooseWordShape, chooseBoolShape, wordNodes, boolNodes, relayWordNodes, relayBoolNodes, chooseWordNodes, chooseBoolNodes, wordResultType, boolResultType, relayWordResultType, relayBoolResultType, wordKey, boolKey, relayWordKey, relayBoolKey, chooseWordKey, chooseBoolKey, wordParameters, boolParameters, relayWordParameters, relayBoolParameters, chooseWordParameters, chooseBoolParameters, wordInstantiation, boolInstantiation, relayWordInstantiation, relayBoolInstantiation, relayWordLoopInstantiation, relayBoolLoopInstantiation, relayWordFinalInstantiation, relayBoolFinalInstantiation, noLocals, profile}

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

theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (wordInput boolInput relayWordInput relayBoolInput chooseWordInput chooseBoolInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      wordInput.row = observed.wordRow.row ∧ boolInput.row = observed.boolRow.row ∧ relayWordInput.row = observed.relayWordRow.row ∧ relayBoolInput.row = observed.relayBoolRow.row ∧ chooseWordInput.row = observed.chooseWordRow.row ∧ chooseBoolInput.row = observed.chooseBoolRow.row ∧
      ∃ (wordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued wordInput)
        (boolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued boolInput)
        (relayWordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayWordInput)
        (relayBoolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued relayBoolInput)
        (chooseWordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseWordInput)
        (chooseBoolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseBoolInput),
      ∃ (wordHeader : ActualHeader fixture observed.wordRow.row)
        (boolHeader : ActualHeader fixture observed.boolRow.row)
        (relayWordHeader : ActualHeader fixture observed.relayWordRow.row)
        (relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row)
        (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
        (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row),
        wordHeader.header = wordPacket.header ∧ boolHeader.header = boolPacket.header ∧ relayWordHeader.header = relayWordPacket.header ∧ relayBoolHeader.header = relayBoolPacket.header ∧ chooseWordHeader.header = chooseWordPacket.header ∧ chooseBoolHeader.header = chooseBoolPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons wordPacket (.cons boolPacket (.cons relayWordPacket (.cons relayBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))) := by
  obtain ⟨wordInput, wordRow, wordPacket, wordHeader, wordEq, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolRow, boolPacket, boolHeader, boolEq, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨relayWordInput, relayWordRow, relayWordPacket, relayWordHeader, relayWordEq, relayWordSlot, relayWordSignature⟩ := observed.relayWordRow.issue
  obtain ⟨relayBoolInput, relayBoolRow, relayBoolPacket, relayBoolHeader, relayBoolEq, relayBoolSlot, relayBoolSignature⟩ := observed.relayBoolRow.issue
  obtain ⟨chooseWordInput, chooseWordRow, chooseWordPacket, chooseWordHeader, chooseWordEq, chooseWordSlot, chooseWordSignature⟩ := observed.chooseWordRow.issue
  obtain ⟨chooseBoolInput, chooseBoolRow, chooseBoolPacket, chooseBoolHeader, chooseBoolEq, chooseBoolSlot, chooseBoolSignature⟩ := observed.chooseBoolRow.issue
  refine ⟨wordInput, boolInput, relayWordInput, relayBoolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, relayWordRow, relayBoolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, relayWordPacket, relayBoolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, relayWordHeader, relayBoolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, relayWordEq, relayBoolEq, chooseWordEq, chooseBoolEq, ?_⟩
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.wordRow.index ∨ index = observed.boolRow.index ∨ index = observed.relayWordRow.index ∨ index = observed.relayBoolRow.index ∨ index = observed.chooseWordRow.index ∨ index = observed.chooseBoolRow.index := by
    have contained := of_decide_eq_true (List.all_eq_true.mp observed.indexCoverage index (List.mem_range.mpr bound))
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using contained
  rcases casesIndex with same | same | same | same | same | same
  · refine ⟨wordHeader.header, ?_, wordSlot.trans same.symm, ?_⟩
    · rw [wordEq]; exact .head _
    · rw [same, observed.wordRow.slot.selected] at found
      exact wordSignature.trans (Option.some.inj found)
  · refine ⟨boolHeader.header, ?_, boolSlot.trans same.symm, ?_⟩
    · rw [boolEq]; exact .tail _ (.head _)
    · rw [same, observed.boolRow.slot.selected] at found
      exact boolSignature.trans (Option.some.inj found)
  · refine ⟨relayWordHeader.header, ?_, relayWordSlot.trans same.symm, ?_⟩
    · rw [relayWordEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.relayWordRow.slot.selected] at found
      exact relayWordSignature.trans (Option.some.inj found)
  · refine ⟨relayBoolHeader.header, ?_, relayBoolSlot.trans same.symm, ?_⟩
    · rw [relayBoolEq]; exact .tail _ (.tail _ (.tail _ (.head _)))
    · rw [same, observed.relayBoolRow.slot.selected] at found
      exact relayBoolSignature.trans (Option.some.inj found)
  · refine ⟨chooseWordHeader.header, ?_, chooseWordSlot.trans same.symm, ?_⟩
    · rw [chooseWordEq]; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
    · rw [same, observed.chooseWordRow.slot.selected] at found
      exact chooseWordSignature.trans (Option.some.inj found)
  · refine ⟨chooseBoolHeader.header, ?_, chooseBoolSlot.trans same.symm, ?_⟩
    · rw [chooseBoolEq]; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · rw [same, observed.chooseBoolRow.slot.selected] at found
      exact chooseBoolSignature.trans (Option.some.inj found)
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
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its scalar output is obtained from the actual public execution. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed, .bool true, .bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed, .bool true, .bool true] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed, .bool true, .bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed, .bool true, .bool true] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        if returned : completion.value = .word seed then
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, returned⟩
        else throw (IO.userError "generic initial output changed")


end Tests.SourceCoreEvidenceScoped
