import Solcore.Test.SourceCoreGeneralizedExportPublic
import Solcore.Test.SourceCoreGeneralizedExportObserved
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicAcceptedNamedForward
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedReturnCoverage
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceLifting

/-! The accepted-body public theorems at one actual named row. `tick` of the
unchanged three-function program returns its parameter. A runtime check places
every expression node of its body in the closed expression subset, the return
inversion covers its accepted tree, and the compile receipts and the lifted
Source trace supply the remaining inputs. Together with the existing start
receipts they meet every premise of the named-row output, checkpoint and root
theorems at its first public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CellAwareInvocationAcceptedExpressionTrees (Subset)
open CellAwareInvocationAcceptedNamedHeaders (index)

/-- A cache row with the key of `row`, at which every expression node of the
row's original body is checked to be a closed-subset site. -/
structure ClosedRow (fixture : ProfiledFixture) (row : Row fixture.original) where
  named : SourceCoreGeneralFunctions.Function
  key : named.signature.key = row.original.key
  nodes : ∀ id node, row.original.function.typedBody.lookupExpression? id = some node →
    Subset fixture.original.recipe.compiled.indexed named row.original.function.typedBody id

def observeClosedRow (fixture : ProfiledFixture) (row : Row fixture.original) : IO (ClosedRow fixture row) := do
  match found : fixture.original.recipe.compiled.indexed.base.functions.find?
      (fun named => decide (named.signature.key = row.original.key)) with
  | none => throw (IO.userError "accepted tick cache row")
  | some named =>
    let some ⟨nodes⟩ := CellAwareInvocationAcceptedSubsetCheck.nodes? fixture.original.recipe.compiled.indexed
        named row.original.function.typedBody
      | throw (IO.userError "accepted tick outside the closed expression subset")
    return ⟨named, by simpa using List.find?_some found, nodes⟩

variable {fixture : ProfiledFixture} {whole : WholeInventory fixture} {row : Row fixture.original}

/-- The first public call of the row, with the conclusions of the accepted-body
output theorem, the checkpoint sufficiency theorem and the checkpoint
reflection theorem. -/
structure AcceptedTick (selected : SelectedInventory whole row) (flag : Bool)
    (started : Started fixture.original row.original.key [.bool flag]) where
  start : SelectedCompilationPublicSessionInitial.Started whole.rows fixture.ready selected.packet.header started.call
  output : ∃ requiredExecution requiredOutput, ∀ executionFuel outputFuel
      (outcome : SourceCoreExecution.Outcome started.artifact),
    requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
    started.call.checkpoint.ResumeAt executionFuel outputFuel outcome →
    ∃ (returned : SourceCoreExecution.Completion started.artifact)
      (actual : SourceCoreIndexedSession.Completion start.artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store),
      outcome = .succeeded returned ∧
      start.checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      returned.IndexedAt actual
  native : ∃ (value : Value) (finalStore : Store) (required : Nat),
    ∀ fuel, required ≤ fuel → start.checkpoint.NativeDone fuel value finalStore
  reflects : ∀ fuel (value : Value) (finalStore : Store), start.checkpoint.NativeDone fuel value finalStore →
    ∃ (sidecar : SourceCoreStageContracts.Sidecar) (size : Nat) (environment : Dynamic.Environment)
      (bound : Dynamic.Heap) (finalContext : SourceSemantics.Context) (outcome : Staging.Recursive.BodyOutcome)
      (after : Dynamic.Heap),
      Dynamic.BindersAllocate [] ⟨[]⟩ selected.packet.header.function.parameters [.bool flag] environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled) size
        (RecursiveStageRegistry.scope sidecar [] selected.packet.header.function) selected.packet.header.context
        environment bound selected.packet.header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult selected.packet.header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome)

/-- Every premise is an original checked or static observation, a runtime check
of the row's expression nodes, or an actual public start. The staged Source
trace is lifted from the row's independent Source execution. -/
theorem accepted_tick (selected : SelectedInventory whole row) (shape : TickShape row.original.function.typedBody)
    (closedRow : ClosedRow fixture row) (flag : Bool)
    (wellFormed : ProgramWellFormed (Program.ofChecked fixture.original.recipe.compiled.sourceProgram))
    (started : Started fixture.original row.original.key [.bool flag])
    (callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true) :
    Nonempty (AcceptedTick selected flag started) := by
  have support := SelectedCompilationNamedSupport.Support.of_program wellFormed
  obtain ⟨start⟩ := CellAwarePublicInitialSelectedStart.from_selected_call
    (rows := whole.rows) (prepared := fixture.ready) (header := selected.packet.header) (call := started.call)
    fixture.original.accepted fixture.original.selected started.opened started.bootstrap started.fresh
    started.authority (.single started.ready) (fun _ member key => selected.root_selection member key)
  let actualShape := selected.tick_shape shape
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      selected.packet.header.function.context [.bool flag] selected.packet.header.types := by
    rw [selected.tick_input_types actualShape]
    exact .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.bool flag] [.bool flag] :=
    .cons ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩ .nil
  obtain ⟨origin, _contextAt, _issued, _extension⟩ := CellAwarePublicInitialStart.receiver start
  obtain ⟨initial⟩ := CellAwarePublicInitialStart.of_started whole.distinct callableProfile
    origin.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults origin.result.diagnostics)
    support.bodyTyping start inputTypes inputMeanings
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued selected.input.prepared selected.packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨selected.packet.selected.diagnostics, selected.packet.selected.found, rfl⟩
  obtain ⟨sidecar, _sidecarIssued, bodySelected⟩ := selected.invocation
  have namedSame : prepared.named.specialized = row.original := prepared.same.trans selected.original
  have keyEq : closedRow.named.signature.key = prepared.named.signature.key :=
    closedRow.key.trans ((CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_key _ prepared.selected).trans
      (congrArg (·.key) namedSame)).symm
  have sourceSame : CallableIndexedNamedGeneration.source prepared.named = row.original.function.typedBody :=
    congrArg (fun specialized => specialized.function.typedBody) namedSame
  have headerSource : selected.packet.header.function.source = CallableIndexedNamedGeneration.source prepared.named :=
    selected.source_eq.trans sourceSame.symm
  have closed : CellAwareInvocationAcceptedExpressions.Closed (index prepared selected.packet.aligned) :=
    CellAwareInvocationAcceptedSubsetCheck.closed prepared.compilation _ keyEq (by rw [sourceSame]; exact closedRow.nodes)
  obtain ⟨body⟩ := (index prepared selected.packet.aligned).body_receipt
  have statementsEq : (index prepared selected.packet.aligned).statements = [actualShape.returned.id] := by
    have same : selected.packet.header.function.body = prepared.compilation.statements := by
      rw [selected.packet.aligned.function]
      rfl
    exact same.symm.trans (selected.tick_statements actualShape)
  have returnedFound : (index prepared selected.packet.aligned).compilerSource.lookupStatement? actualShape.returned.id =
      some actualShape.returned := by
    change (CallableIndexedNamedGeneration.source prepared.named).lookupStatement? _ = _
    rw [← headerSource]
    exact actualShape.returnedFound
  obtain ⟨sourceCompiled, artifact, checked⟩ := CellAwarePublicAcceptedNamedRoot.compilation_receipts
    fixture.original.checked fixture.original.accepted fixture.original.selected
  obtain ⟨allocated, sourceTrace⟩ := selected.tick_source_body actualShape ⟨[]⟩ flag
  obtain ⟨_sourceSize, measured⟩ := RecursiveNamedCallBounds.FunctionOutcome.has_size (.control sourceTrace)
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      selected.packet.header.function.source actualShape.read.node.id selected.packet.header.function.body := by
    rw [selected.tick_statements actualShape]
    exact .returning [] actualShape.returnedFound actualShape.returnedForm
  have nodes : ∀ id node, selected.packet.header.function.source.lookupExpression? id = some node →
      Subset fixture.original.recipe.compiled.indexed closedRow.named selected.packet.header.function.source id := by
    rw [selected.source_eq]
    exact closedRow.nodes
  obtain ⟨_stagedSize, trace⟩ := CellAwareInvocationAcceptedSourceLifting.returned
    (registry := SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).source bodySelected)
    ((SelectedCompilationPhysicalProgramSupport.stages fixture.original.recipe.compiled).evidence bodySelected)
    (support.certified selected.packet.header).runtime.graph.nodeOccurrencesUnique terminal
    (nodes _ _ actualShape.read.found) measured
  have covered := CellAwareInvocationAcceptedReturnCoverage.returning (index prepared selected.packet.aligned) body.tree
    (semantic := (index prepared selected.packet.aligned).source)
    (expected := selected.packet.header.function.resultType)
    (admitted := CellAwareInvocationAcceptedMatches.Admitted (index prepared selected.packet.aligned))
    (generalized := CellAwareInvocationAcceptedInputs.Generalized (attachment := fun _ _ _ => True)
      (index prepared selected.packet.aligned))
    statementsEq returnedFound actualShape.returnedForm
  obtain ⟨_capture, _value, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput, _result, output⟩ :=
    CellAwarePublicAcceptedNamedForward.first_value_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
      initial.heaps rfl start.started start.atCheckpoint
      (congrArg SourceCoreCompatibleValues.Context.registry initial.contextAt) initial.exportsReady allocated trace
  obtain ⟨_capture, value, finalStore, _finalMap, _finalWorld, required, run, _result⟩ :=
    CellAwarePublicAcceptedNamedRoot.checkpoint_has_sufficient_fuel_selected callableProfile initial.issued prepared
      selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
      initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
      initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
      initial.heaps rfl start.started allocated trace
  refine ⟨⟨start, ⟨requiredExecution, requiredOutput, ?_⟩, ⟨value, finalStore, required, run⟩, ?_⟩⟩
  · intro executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    obtain ⟨returned, actual, generation, _reached, same, succeeded, indexed, _⟩ :=
      output executionFuel outputFuel outcome enoughExecution enoughOutput resumed
    exact ⟨returned, actual, generation, _, _, same, succeeded, indexed⟩
  · intro fuel completedValue completedStore completed
    obtain ⟨_capture, size, environment, bound, finalContext, outcome, after, _finalMap, _finalWorld,
        bound', staged, result, _named⟩ :=
      CellAwarePublicAcceptedNamedRoot.checkpoint_reflects_selected callableProfile initial.issued prepared
        selected.packet.aligned fixture.ready diagnostic support start.selected (owner fixture.original.recipe.compiled)
        initial.caller.base.val initial.globalReference initial.keyPhysical initial.caller.physical initial.stable
        initial.heapTyped initial.argumentsTyped bodySelected closed artifact checked body covered initial.represented
        initial.heaps rfl start.started completed
    exact ⟨sidecar, size, environment, bound, finalContext, outcome, after, bound', staged, result⟩

namespace AcceptedTickRuntime

/-- Each call starts a fresh actual session. The plan is kernel-checked against
whatever the observed compile, check and start receipts are; the resume runs the
real compiled code. -/
def run : IO Unit := do
  let observed ← observe
  let closedRow ← observeClosedRow observed.fixture observed.tick
  for flag in [true, false] do
    let started ← observeStarted observed.fixture.original observed.tick.original.key [.bool flag]
    have _plan : ∃ (whole : WholeInventory observed.fixture) (selected : SelectedInventory whole observed.tick),
        Nonempty (AcceptedTick selected flag started) := by
      obtain ⟨whole⟩ := observed.fixture.inventory observed.cache observed.typing.wellFormed
      obtain ⟨selected⟩ := whole.select observed.tick
      exact ⟨whole, selected, accepted_tick selected observed.tickShape closedRow flag observed.typing.wellFormed
        started observed.callableProfile⟩
    let result ← started.call.checkpoint.resumeWithReceipt runOptions.executionFuel runOptions.outputValidationFuel
    match result.val with
    | .succeeded returned =>
      unless returned.value == .bool flag do throw (IO.userError "accepted tick output changed")
    | _ => throw (IO.userError "accepted tick call did not succeed")
  IO.println "ACCEPTED_TICK_PUBLIC_PASS"

end AcceptedTickRuntime

end Tests.SourceCoreGeneralizedExport
