import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentEntryReceipts
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryArgumentBundles
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadSource

/-! The actual initialized fixture callee and original Source parent children
supply one admitted argument sequence and literal application. The returned
caller keeps all maps, worlds, rows, heap typing and the original whole pool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

universe u
variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {mapping : LocationMap} {world : StoreTyping} {actualCapture : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actualCapture)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)
  (history : History (chosen.chosen.formation.code []))
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming} {location : Dynamic.Location}

local notation "index" => CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext
local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "localContext" => SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture
local notation "parentScope" => SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture

variable (evidence : Dynamic.EvidenceEnvironment)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture) environment canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext fixture.packet.compiled.indexed.layouts.definitions)
  (stored : CallableIndexedOwnedChosenOrdinaryStoredMembers.ChosenStoredAt root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.index chosen.chosen [] captured prefixContext) history before store location)
  (lookup : Dynamic.Environment.LooksUp environment fixture.graph.binder.id location)
  (initial : callerProtocol.State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) initial)

include stored lookup in
/-- Only the readable ordinary Source cell determines this callee outcome.
The known trace comes from the original initialized read producer. -/
private theorem callee_outcome {knownSize : Nat}
    (known : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      knownSize localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 9) (.closure (index).function) before)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      localContext evidence (source fixture.packet.named) environment before (expressionId fixture.packet 9) outcome after) :
    outcome = .value (.closure (index).function) ∧ after = before := by
  obtain ⟨_member, target, _reference, read, _nativeRead⟩ := stored
  exact CompatibleExpressionReads.source_outcome_unique fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    (lookupExpression?_sound fixture.graph.calleeFound) fixture.graph.calleeForm fixture.parentRows.calleeCoercions
    lookup read rfl trace (.value known.sound)

include stored lookup in
/-- Finite inversion retains the original measured Source callee, ordered
argument child and closure call; the actual initialized read excludes earlier
faults without a whole-language preservation assumption. -/
private theorem called_at_parent {knownSize : Nat}
    (known : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      knownSize localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 9) (.closure (index).function) before)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 5) outcome after) :
    ∃ calleeSize argumentsSize callSize arguments,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        calleeSize localContext evidence (source fixture.packet.named) environment before
        (expressionId fixture.packet 9) (.closure (index).function) before ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
        argumentsSize localContext evidence (source fixture.packet.named) environment before
        [expressionId fixture.packet 6] arguments before ∧
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        callSize localContext evidence (index).function.evidence before (.closure (index).function) arguments outcome after ∧
      calleeSize < size ∧ argumentsSize < size ∧ callSize < size := by
  have original := CallableIndirectCallSourceBounds.indirect_inv_sized fixture.graph.parentFound
    fixture.graph.parentForm fixture.graph.parentCoercions
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace
  cases original with
  | calleeFault child _ =>
    obtain ⟨same, _⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.fault child.sound)
    cases same
  | notCallable child invalid _ =>
    obtain ⟨same, _⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value child.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    exact False.elim (invalid trivial)
  | argumentsFault first _ failed _ _ =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    exact False.elim (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.noFault fixture _ _ _ failed)
  | sourceArity _ _ mismatch _ _ => exact False.elim (mismatch rfl)
  | argumentCoercionFault _ _ _ _ failed _ _ _ =>
    change SourceExecutionSize.CoercionPathFaults _ _ _ _ _ [] _ _ _ at failed
    cases failed
  | applied _ first args packed converted unpacked sourceArity appliedArity called calleeSmall argsSmall _ callSmall =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    obtain ⟨valuesEq, heapEq⟩ := SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture args
    subst heapEq
    change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ [] _ _ _ at converted
    cases converted
    have argumentsEq := Dynamic.ValuesPack.injective_of_length_eq packed unpacked (by
      rw [valuesEq]; exact appliedArity.symm)
    subst argumentsEq
    exact ⟨_, _, _, _, first, args, call_with_closure_evidence (.value called), calleeSmall, argsSmall, callSmall⟩
  | applicationFault first args packed converted unpacked sourceArity appliedArity called calleeSmall argsSmall _ callSmall =>
    obtain ⟨same, heaps⟩ := callee_outcome fixture root chosen captured prefixContext history evidence stored lookup known (.value first.sound)
    cases Dynamic.ExpressionOutcome.value.inj same
    subst heaps
    obtain ⟨valuesEq, heapEq⟩ := SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture args
    subst heapEq
    change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ [] _ _ _ at converted
    cases converted
    have argumentsEq := Dynamic.ValuesPack.injective_of_length_eq packed unpacked (by
      rw [valuesEq]; exact appliedArity.symm)
    subst argumentsEq
    exact ⟨_, _, _, _, first, args, call_with_closure_evidence (.fault called), calleeSmall, argsSmall, callSmall⟩

include atHeader shape typing inventory captured prefixContext history extension environments heaps locals agrees typed stored lookup admitted in
/-- The original whole Source parent runs its initialized callee, one admitted
ordered argument sequence and the literal application. The result retains the
actual restored caller pool and successful Source admission. -/
theorem preserves_parent_at_initialized (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size localContext evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 5) outcome after)
    (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (fixture.calls.parent.expression.rename ξ) result finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt
        (context := localContext) (registry := registry) (faults := faults)
        bridge functions chosen.parent.compiler initial outcome after result finalStore finalMap finalWorld := by
  obtain ⟨knownSize, known, calleePost, _selection, _stored⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.callee_at_parent fixture atHeader root chosen
      bridge typing inventory evidence extension environments heaps locals agrees stored lookup initial admitted
  obtain ⟨calleeSize, argumentsSize, callSize, arguments, _actualCallee, argumentsTrace, called,
      _calleeSmall, argumentsSmall, callSmall⟩ :=
    called_at_parent fixture root chosen captured prefixContext history evidence stored lookup known trace
  obtain ⟨pair, codes, tree, childPreserves, _childReflects⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.pair_at_chosen_parent fixture atHeader root chosen
      bridge functions typing evidence (registry := registry) (faults := faults)
  obtain ⟨dispatchReceipt⟩ := CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport.at_chosen_parent
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    chosen.parent.compiler chosen.parent.prepared (congrArg source atHeader.named.symm) stored.1
  let dispatch : CallStageBoundary.Dispatch (CallableLedger.frame dispatchReceipt.sidecar) chosen.parent.prepared.site
      chosen.parent.prepared.site.call [expressionId fixture.packet 6] (.closure (index).function)
      (value (index).code (index).captured.embedding history.native (index).capturedActual) :=
    ⟨dispatchReceipt.dispatch.function, dispatchReceipt.dispatch.contract, dispatchReceipt.dispatch.row,
      dispatchReceipt.dispatch.guard, dispatchReceipt.dispatch.shape, dispatchReceipt.dispatch.found,
      dispatchReceipt.dispatch.attached, dispatchReceipt.dispatch.call_eq.trans chosen.parent.prepared.call.symm,
      dispatchReceipt.dispatch.arguments_eq, dispatchReceipt.dispatch.stages, dispatchReceipt.dispatch.bound⟩
  have selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected dispatchReceipt.sidecar
      chosen.parent.prepared.site (expressionId fixture.packet 9) [expressionId fixture.packet 6]
      indirectMetadata chosen.parent.compiler.original dispatch.row := by
    simpa only [dispatch] using dispatchReceipt.selected
  obtain ⟨calleeEvaluation, represented, calleeHeaps, calleeMaps, calleeWorlds,
    calleeFrame, calleeMetadata, calleeState, calleeRelated, calleePostAdmission⟩ := calleePost
  let calleeNative := value (index).code (index).captured.embedding history.native (index).capturedActual
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))
      canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons represented.runtime_hasType (typed.weaken calleeWorlds))
  have argumentTyping : ExpressionsHaveTypes (source fixture.packet.named) localContext
      [expressionId fixture.packet 6] [parameterType] :=
    .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.argument_typed typing) (.nil _)
  have actualTree : DataExpressionSequence.Tree (source fixture.packet.named)
      (SourceCoreChosenOrdinaryAcceptedPairArgumentBounds.Tuple fixture
        (SourceCoreChosenOrdinaryAcceptedParentEntryReceipts.fixture_root fixture atHeader root) pair)
      parentScope [expressionId fixture.packet 6] [parameterType] chosen.parent.compiler.codes := by
    rw [codes]
    exact tree
  obtain ⟨payloads, argumentStore, argumentMap, argumentWorld, argumentEvaluation, values, argumentHeaps,
      maps, worlds, frame, metadata, argumentState, argumentRelated, argumentAdmission⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget actualTree
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique argumentTyping (fun childSize _ => childPreserves childSize)
      (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) layout actualTyped
      calleeState calleePostAdmission.at_value.2 argumentsTrace (Nat.le_trans (Nat.le_of_lt argumentsSmall) within)
  have arity : (index).function.parameters.length = arguments.length := by
    change (chosen.chosen.formation.function []).parameters.length = arguments.length
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters, (SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes.values_at fixture argumentsTrace).1]
    rfl
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((index).function.parameters.map (fun binder => binder.scheme.body)) := by
    change TypeSystem.Ty.productMany [parameterType] = TypeSystem.Ty.productMany ((chosen.chosen.formation.function []).parameters.map (fun binder => binder.scheme.body))
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).1,
      shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have parameterValues := CallableIndexedOwnedChosenOrdinaryArgumentBundles.arguments_at_compiler
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    functions represented rfl inventory.contracts maps worlds values arity rawBundle
  have nativeResult := (CallableIndexedOwnedChosenOrdinaryArgumentBundles.compiler_parameters
    root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) stored.1 chosen.parent.compiler
    functions represented rfl).2
  have member := stored.1
  cases member with
  | ordinary owner _factory origin _prefix observed referenceIndex _nativeTyped =>
    have reference : captured.canonical[(index).code.referenceIndex]? =
        some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    obtain ⟨result, finalStore, finalMap, finalWorld, application, resultPost⟩ :=
      SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication.application_preserves fixture atHeader shape typing
        chosen.chosen root chosen.factory bridge functions owner (captured.extend maps worlds) prefixContext history
        origin observed argumentState argumentAdmission argumentHeaps parameterValues reference argumentsTrace
        chosen.parent.compiler chosen.parent.prepared dispatch rfl selected
        budget called (Nat.le_trans (Nat.le_of_lt callSmall) within)
    have accepted := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
      fixture shape atHeader chosen.chosen dispatch selected
      fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown).first
    have read : Evaluates (calleeNative :: actual) store (.second (.var 0))
        (.word dispatch.contract) store :=
      .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
    have gate := chosen.parent.prepared.site.dispatch_known .beforeArguments
      fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
      dispatch.contract dispatch.row dispatch.found read
    rw [SourceCoreCallableContracts.reason_accepted dispatch.row
      chosen.parent.prepared.site.reasonAt .beforeArguments accepted] at gate
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole : Evaluates actual store
        (CallableContract.call chosen.parent.prepared.site.gates
          fixture.packet.compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
          chosen.parent.compiler.resultType (chosen.parent.compiler.calleeCode.expression.rename ξ)
          ((SourceCoreCalls.packArguments chosen.parent.compiler.codes).expression.rename ξ)) result finalStore :=
      LanguageResult.bind_success _ calleeEvaluation
        (LanguageResult.bind_success _ gate (LanguageResult.bind_success _ argumentEvaluation application))
    rw [← chosen.parent.prepared.lowered_rename chosen.parent.compiler ξ] at whole
    obtain ⟨resultRep, lastHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata,
      _nested, _nestedRelated⟩ := resultPost.1
    obtain ⟨returned, returnedRelated, returnedAdmission⟩ := resultPost.2
    have rawResult : SourceCoreRawMetadata.runtimeType chosen.parent.compiler.original.type =
        SourceCoreRawMetadata.runtimeType (index).function.resultType := by
      change SourceCoreRawMetadata.runtimeType chosen.parent.compiler.original.type =
        SourceCoreRawMetadata.runtimeType (chosen.chosen.formation.function []).resultType
      rw [chosen.parent.original, fixture.graph.parentType,
        (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader chosen.chosen []).2.1]
    have parentRep := CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions
      chosen.parent.compiler rawResult nativeResult resultRep
    have parentAdmission : PostAdmission bridge localContext chosen.parent.compiler.original.type outcome returned := by
      rw [chosen.parent.original, fixture.graph.parentType]
      exact returnedAdmission
    exact ⟨result, finalStore, finalMap, finalWorld, whole, parentRep, lastHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated argumentRelated) returnedRelated, parentAdmission⟩

end Tests.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
