import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectPurePrefixBounds

/-! The accepted whole indirect parent uses its original initialized callee,
pair argument and stored lambda application. Actual intermediate posts are
composed at the same reached states; initial heap and stored-cell authority
remain genuine inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)

universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured capturedActual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)


variable {history : History ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location}
  (initial : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), mapping, world, heap, store, canonical⟩)

include atHeader in
/-- Compose the genuine argument and application posts. This finite helper
only projects retained witnesses and does not execute or restore a second time. -/
private theorem result_at_parent
    {middleMap finalMap : LocationMap} {middleWorld finalWorld : StoreTyping}
    {middle after : Dynamic.Heap} {argumentStore finalStore : Store}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (argumentState : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), middleMap, middleWorld, middle, argumentStore, canonical⟩)
    (related : callerProtocol.Relates initial argumentState)
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    (frame : AdministrativePreserved mapping store middleMap argumentStore)
    (metadata : Dynamic.HeapMetadataExtend heap middle)
    (nativeResult : (chosen.parent.compiler).resultType = ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code.receipt.resultCore)
    (result : CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt
      (registry := registry) (faults := faults) (((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.extend maps worlds) ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
      (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld)
    (returned : callerProtocol.State ⟨(SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture), finalMap, finalWorld, after, finalStore, canonical⟩)
    (returnedRelated : callerProtocol.Relates argumentState returned)
    (post : PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) wordType outcome returned) :
    CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt (registry := registry) (faults := faults)
      (context := (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)) bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler initial outcome after value finalStore finalMap finalWorld := by
  have rawType : (chosen.parent.compiler).original.type = wordType := by
    rw [chosen.parent.original, fixture.graph.parentType]
  have resultType : ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function.resultType = wordType :=
    (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).2.1
  have rawResult : SourceCoreRawMetadata.runtimeType (chosen.parent.compiler).original.type =
      SourceCoreRawMetadata.runtimeType ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function.resultType := by rw [rawType, resultType]
  obtain ⟨represented, heaps, finalMaps, finalWorlds, finalFrame, finalMetadata, _reached, _related⟩ := result
  unfold CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
  refine ⟨CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler
      rawResult nativeResult represented, heaps, maps.trans finalMaps, worlds.trans finalWorlds,
    frame.trans finalFrame, metadata.trans finalMetadata, returned,
    callerProtocol.trans related returnedRelated, ?_⟩
  simpa only [rawType] using post

variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
    environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap ((SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext fixture.packet.compiled.indexed.layouts.definitions)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) history heap store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include atHeader shape typing extension environments heaps locals agrees typed stored lookup admitted in
/-- Whole Core completion reflects to the independent Source parent and the
same admitted returned caller. Callee execution, argument meanings, guards,
dispatch and native parameter alignment are derived inside this proof. -/
theorem reflects_parent_at_initialized (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (fixture.calls.parent.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named) environment heap
        (expressionId fixture.packet 5) outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt (registry := registry) (faults := faults)
        (context := (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)) bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler initial
        outcome after value finalStore finalMap finalWorld := by
  obtain ⟨pair, sameCodes, argumentTree, _preserves, reflects⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.pair_at_chosen_parent
      fixture atHeader root chosen bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) typing evidence (registry := registry) (faults := faults)
  have tree : DataExpressionSequence.Tree (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture
        (SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.fixture_root fixture atHeader root) pair)
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [expressionId fixture.packet 6] [parameterType] (chosen.parent.compiler).codes := by
    simpa only [sameCodes] using argumentTree
  have argumentsTyped : ExpressionsHaveTypes (source fixture.packet.named) (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      [expressionId fixture.packet 6] [parameterType] :=
    .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.argument_typed typing) (.nil _)
  obtain ⟨calleeSize, calleeTrace, calleePost, _selected, _stored⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.callee_at_parent fixture atHeader root chosen
      bridge typing inventory evidence extension environments heaps locals agrees stored lookup initial admitted
  obtain ⟨selection⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport.at_chosen_parent
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    chosen.parent.compiler chosen.parent.prepared (congrArg source atHeader.named).symm stored.1
  let dispatch : CallStageBoundary.Dispatch (CallableLedger.frame selection.sidecar)
      (chosen.parent.prepared).site (chosen.parent.prepared).site.call [expressionId fixture.packet 6]
      (.closure ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).function) (CallableIndexedLambdaValues.value ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code
        ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.embedding history.native ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).capturedActual) := {
    function := selection.dispatch.function, contract := selection.dispatch.contract,
    row := selection.dispatch.row, guard := selection.dispatch.guard,
    shape := selection.dispatch.shape, found := selection.dispatch.found,
    attached := selection.dispatch.attached,
    call_eq := selection.dispatch.call_eq.trans chosen.parent.prepared.call.symm,
    arguments_eq := selection.dispatch.arguments_eq, stages := selection.dispatch.stages,
    bound := selection.dispatch.bound }
  have accepted := SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader chosen.chosen dispatch selection.selected
    fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  have parameters := CallableIndexedOwnedChosenOrdinaryArgumentBundles.compiler_parameters
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1
    chosen.parent.compiler (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) calleePost.2.1 rfl
  obtain ⟨_original, step, _passed⟩ := CallableIndexedOwnedStoredIndirectPurePrefixBounds.reflects_parent
    bridge (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts) chosen.parent.compiler chosen.parent.prepared tree fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    argumentsTyped environments locals agrees typed initial calleePost dispatch selection.selected accepted
    (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.noFault fixture) calleeTrace budget
    (fun size _ => reflects size) completed within
  obtain ⟨owner, _factory, origin, _prefix, globals, referenceIndex, _nativeTyped⟩ := stored.1
  have reference : ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).captured.canonical[((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext)).code.referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [referenceIndex]
    exact globals.reference
  obtain ⟨_nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, values, argumentHeaps, stepMaps, stepWorlds,
    _stepFrame, _stepMetadata, cumulativeMaps, cumulativeWorlds, cumulativeFrame, cumulativeMetadata,
    ⟨argumentState, related, argumentAdmission⟩, remainingSize, remaining, remainingStrict⟩ := step
  let current := (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).captured.extend stepMaps stepWorlds
  have arity : (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).function.parameters.length = arguments.length := by
    change (chosen.chosen.formation.function []).parameters.length = arguments.length
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters, (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture argumentsTrace).1]
    rfl
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext).function.parameters.map (fun binder => binder.scheme.body)) := by
    change TypeSystem.Ty.productMany [parameterType] = TypeSystem.Ty.productMany ((chosen.chosen.formation.function []).parameters.map (fun binder => binder.scheme.body))
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have actualArguments := CallableIndexedOwnedChosenOrdinaryArgumentBundles.arguments_at_compiler
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    calleePost.2.1 rfl inventory.contracts stepMaps stepWorlds values arity rawBundle
  obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.application_reflects
      (registry := registry) (faults := faults)
      (atHeader := atHeader) (shape := shape) (typing := typing) (receipt := chosen.chosen)
      (root := root) (chosen := chosen.factory) (bridge := bridge)
      (functions := CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
        (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
      (owner := owner) (captured := current) (prefixContext := rfl) (history := history)
      (origin := origin) (observed := globals) (argumentState := argumentState) (admitted := argumentAdmission)
      (heaps := argumentHeaps) (represented := actualArguments) (reference := reference)
      (argumentsTrace := argumentsTrace) (compiler := chosen.parent.compiler) (prepared := chosen.parent.prepared)
      (dispatch := dispatch) (sameNative := rfl) (selected := selection.selected)
      fixture budget remaining (Nat.le_of_lt remainingStrict)
  obtain ⟨sourceSize, parentTrace⟩ := SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.parent_source
    fixture chosen.chosen calleeTrace argumentsTrace called
  obtain ⟨applicationResult, returned, returnedRelated, post⟩ := result
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, parentTrace,
    result_at_parent fixture atHeader inventory root chosen bridge captured prefixContext initial
      argumentState related cumulativeMaps cumulativeWorlds cumulativeFrame cumulativeMetadata parameters.2
      applicationResult returned returnedRelated post⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
