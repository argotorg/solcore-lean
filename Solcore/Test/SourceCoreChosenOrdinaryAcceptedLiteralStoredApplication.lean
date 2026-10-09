import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralInvocation
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralCallGuard
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectApplicationPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredApplicationProjection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinarySelectedCallReceipts

/-! The accepted fixture's actual ordered pair supplies the raw call arguments.
At the genuine current argument state, its chosen singleton-return invocation
closes the original fourth bind without a whole-body or family meaning input.
The original physical restoration is performed by the invocation producer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters

variable (fixture : AcceptedFixture)

/-- The one actual argument occurrence fixes its value and unchanged Source
heap; this is an inversion of the retained Source trace, not a new execution. -/
theorem arguments_at {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {size : Nat}
    (trace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before [expressionId fixture.packet 6] arguments after) :
    arguments = [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] ∧ after = before := by
  cases trace.sound with
  | cons head tail =>
    obtain ⟨sameValue, sameHeap⟩ := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argument_outcome fixture (.value head)
    cases sameHeap
    cases Dynamic.ExpressionOutcome.value.inj sameValue
    cases tail
    exact ⟨rfl, rfl⟩

variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    {lambdaLowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lambdaLowered)
    {rootFuel : Nat}
    (root : CallableIndexedOwnedLiteralReturnSiteShells.LiteralRootReceipt (compiled := fixture.packet.compiled) caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
      rootFuel (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
      lambdaLowered)
    (chosen : CallableIndexedOwnedPreparedMixedBodySiteInputs.ChosenFactory root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) receipt)

/-- The actual selected numeric row rules out every fault of the returned
literal and fixes its unchanged heap in the genuine parameter context. -/
private theorem literal_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      shape.bodyContext [] (source fixture.packet.named) environment before
      (expressionId fixture.packet 3) outcome after) :
    outcome = .value (.word (Word.ofNatModulo 7)) ∧ after = before := by
  have unique := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have found := fixture.graph.literalFound
  have sameNode : ∀ other, ContainsExpression (source fixture.packet.named) (expressionId fixture.packet 3) other →
      other = fixture.graph.literal := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have nonlocal : ∀ name binder, fixture.graph.literal.form ≠ .reference name (.local binder) := by
    intros
    rw [fixture.graph.literalForm]
    simp
  have proves := numeric_requirement (context := shape.bodyContext) fixture.runtime.rows (Or.inl rfl)
  have selected : NumericLiteralEvidenceReceipts.Selected numericRows literalResolution (.builtin .intWord) :=
    ⟨wordRequirement 0, by simp [numericRows, wordRequirement, literalResolution], rfl, rfl⟩
  have safe := selected.safe (context := shape.bodyContext) fixture.runtime.rows
    (numeric_runtime_ledger (context := shape.bodyContext) fixture.runtime.rows) []
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro other raw path =>
      have same := sameNode _ other
      subst same
      rw [fixture.graph.literalCoercions] at path
      cases path
      rw [fixture.graph.literalForm] at raw
      cases raw with
      | integerLiteral _ constructed =>
        have expected : Dynamic.ResolvedIntegerLiteralConstructs shape.bodyContext (.decimal "7")
            literalResolution (.word (Word.ofNatModulo 7)) := .word (numericLiteralValue?_sound rfl) proves
        exact ⟨congrArg _ (constructed.functional expected), rfl⟩
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
  | @fault _ _ reason failed =>
    have rawFault : Dynamic.ExpressionFormFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
        shape.bodyContext [] (source fixture.packet.named) environment before
        fixture.graph.literal.form fixture.graph.literal.requirements fixture.graph.literal.coercions reason after := by
      cases failed with
      | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
      | form contains failed => exact sameNode _ contains ▸ failed
      | coercion contains _ failed =>
        have same := sameNode _ contains
        subst same
        rw [fixture.graph.literalCoercions] at failed
        cases failed
      | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
      | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
        exact False.elim (nonlocal _ _ (sameNode _ contains ▸ otherForm))
    rw [fixture.graph.literalForm] at rawFault
    cases rawFault with
    | integerRequirement _ unavailable => exact False.elim (safe unavailable)

/-- The actual explicit return admits only the selected Word result; the
finite Source statement inversions preserve the parameter heap exactly. -/
private theorem return_outcome {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome} {size : Nat}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true (Program.ofChecked fixture.packet.compiled.sourceProgram)
      shape.bodyContext [] (source fixture.packet.named) environment before
      [statementId fixture.packet 2] finalContext outcome after) :
    outcome = .returned (.word (Word.ofNatModulo 7)) ∧ after = before := by
  have unique := fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
  have found := lookupStatement?_sound fixture.graph.returnedFound
  have inverted := RecursiveNamedStatementSourceBounds.cons_inv unique found
    (by intro _ _ expression; rw [fixture.graph.returnedForm]; simp) trace
  cases inverted with
  | next head _ _ _ =>
    have returned := RecursiveNamedStatementSourceBounds.return_value unique found fixture.graph.returnedForm head
    obtain ⟨_sameContext, child, value, impossible, _evaluated, _strict⟩ := returned
    cases impossible
  | terminal head _ _ =>
    obtain ⟨_sameContext, child, value, result, evaluated, _strict⟩ :=
      RecursiveNamedStatementSourceBounds.return_value unique found fixture.graph.returnedForm head
    obtain ⟨sameValue, sameHeap⟩ := literal_outcome fixture shape (.value evaluated.sound)
    exact ⟨result.trans (congrArg Dynamic.ControlOutcome.returned (Dynamic.ExpressionOutcome.value.inj sameValue)), sameHeap⟩
  | fault head _ =>
    obtain ⟨child, failed, _strict⟩ := RecursiveNamedStatementSourceBounds.return_fault unique found fixture.graph.returnedForm head
    have impossible := (literal_outcome fixture shape (.fault failed.sound)).1
    cases impossible

include atHeader shape in
/-- Real call inversion exposes the original parameter allocation. Its heap
preservation and the literal return prove the final deep Source heap locally. -/
theorem call_heap {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (heapTyped : Dynamic.HeapWellTyped (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) before)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      context evidence (receipt.formation.function []).evidence before (.closure (receipt.formation.function []))
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] outcome after) :
    outcome = .value (.word (Word.ofNatModulo 7)) ∧
    Dynamic.HeapWellTyped (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) after := by
  have parameters := (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1
  have arity : (receipt.formation.function []).parameters.length =
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue].length := by
    rw [parameters, shape.parameters]
    rfl
  obtain ⟨types, bodyContext, environment, bound, extended, allocated, body⟩ := FunctionCallBody.Outcome.trace arity trace.sound
  have entryContext : bodyContext = shape.bodyContext := by
    have original : MonoBindersExtend (receipt.formation.function []).source.owner
        (receipt.formation.function []).context (receipt.formation.function []).parameters [parameterType]
        shape.bodyContext := by
      change MonoBindersExtend (source caller.named).owner (runtimeContext fixture.packet) _ _ _
      simpa only [parameters, atHeader.named] using shape.parameters_extend
    have sameTypes : types = [parameterType] := extended.bodyTypes_eq.symm.trans original.bodyTypes_eq
    subst types
    exact extended.functional original
  have valuesTyped : Dynamic.ValuesHaveTypes (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      before [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue]
      ((receipt.formation.function []).parameters.map (fun binder => binder.scheme.body)) := by
    rw [parameters, shape.parameters]
    simpa only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) before
  have boundTyped := Dynamic.BindersAllocate.preservesHeapTyping heapTyped valuesTyped allocated
  have bodyShape := (SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).2
  have expected : outcome = .value (.word (Word.ofNatModulo 7)) ∧ after = bound := by
    cases body with
    | @returned finalContext result _ executed =>
      obtain ⟨bodySize, executed⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size executed
      change SourceExecutionSize.FunctionStatementsExecute _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at executed
      rw [atHeader.named] at executed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext (.returned result) after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.control executed)
      have same := return_outcome fixture shape actual
      exact ⟨congrArg Dynamic.ExpressionOutcome.value (Dynamic.ControlOutcome.returned.inj same.1), same.2⟩
    | unit resultUnit _ =>
      rw [bodyShape.1] at resultUnit
      cases resultUnit
    | @fault finalContext reason _ failed =>
      obtain ⟨bodySize, failed⟩ := SourceExecutionSize.FunctionStatementsFault.has_size failed
      change SourceExecutionSize.FunctionStatementsFault _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at failed
      rw [atHeader.named] at failed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext (.fault reason) after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.fault failed)
      have impossible := (return_outcome fixture shape actual).1
      cases impossible
    | @escaped finalContext control _ executed escape =>
      obtain ⟨bodySize, executed⟩ := SourceExecutionSize.FunctionStatementsExecute.has_size executed
      change SourceExecutionSize.FunctionStatementsExecute _ bodySize bodyContext [] (source caller.named)
        environment bound _ finalContext _ after at executed
      rw [atHeader.named] at executed
      have actual : RecursiveNamedLoopContracts.ExecutesAt bodySize true (Program.ofChecked fixture.packet.compiled.sourceProgram)
          shape.bodyContext [] (source fixture.packet.named) environment bound [statementId fixture.packet 2]
          finalContext control after := by
        simpa only [RecursiveNamedLoopContracts.ExecutesAt, entryContext, bodyShape.2, atHeader.named] using (RecursiveNamedCallBounds.FunctionOutcome.control executed)
      have same := (return_outcome fixture shape actual).1
      rcases escape with ⟨_, escaped⟩ | ⟨_, escaped⟩ <;> rw [same] at escaped <;> cases escaped
  exact ⟨expected.1, expected.2 ▸ boundTyped⟩


/-- The actual three Source children compose by the original indirect-parent
constructors. Physical argument count follows from this fixture's real trace. -/
theorem parent_source {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before calleeHeap middle after : Dynamic.Heap} {arguments : List Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome} {calleeSize argumentsSize callSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      calleeSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 9)
      (.closure (receipt.formation.function [])) calleeHeap)
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      argumentsSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) callSize
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 5) outcome after := by
  have actualArity : arguments.length = indirectMetadata.argumentCount := by
    rw [(arguments_at fixture argumentsTrace).1]
    rfl
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  cases called with
  | @value result _ applied =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize,
      SourceExecutionSize.stepSize [], callSize], SourceExecutionSize.stepSize []],
      .value (.intro (raw := result) (middle := after) (lookupExpression?_sound fixture.graph.parentFound) ?_ ?_)⟩
    · rw [fixture.graph.parentForm]
      refine .indirectCall ?_ calleeTrace argumentsTrace packing (.nil) packing rfl actualArity applied
      simp [fixture.graph.parentRequirements, fixture.graph.parentCoercions, indirectMetadata, coercionRequirementIds]
    · rw [fixture.graph.parentCoercions]
      exact .nil
  | fault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize,
      SourceExecutionSize.stepSize [], callSize]], .fault (.form (lookupExpression?_sound fixture.graph.parentFound) ?_)⟩
    rw [fixture.graph.parentForm]
    exact .indirectApply calleeTrace argumentsTrace packing (.nil) packing rfl actualArity failed

section Current
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {mapping : LocationMap} {world : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    {arguments : List Dynamic.Value} {payloads : List Value}
    {calleeHeap middle : Dynamic.Heap} {argumentStore : Store}
    {callerScope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    (argumentState : callerProtocol.State ⟨callerScope, mapping, world, middle, argumentStore, canonical⟩)
    (admitted : Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) argumentState)
    (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
      mapping world middle argumentStore)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      mapping world (receipt.formation.code []).receipt.loweredParameters arguments payloads)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    {argumentSize : Nat}
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram)
      argumentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] arguments middle)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {compilerFuel : Nat}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body compilerFuel compilerContext
      (source fixture.packet.named) scope (expressionId fixture.packet 5) (expressionId fixture.packet 9)
      [expressionId fixture.packet 6] metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {sidecar : SourceCoreStageContracts.Sidecar} {calleeNative : Value} {actual : Environment}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) calleeNative)
    (sameNative : calleeNative = CallableIndexedLambdaValues.value (receipt.formation.code [])
      captured.embedding history.native actualEnvironment)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
      (expressionId fixture.packet 9) [expressionId fixture.packet 6] metadata compiler.original dispatch.row)

/-- The actual application result retains its original whole-pool transition
and a genuine successful Source admission at the same returned caller. -/
def ReturnedAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
    (receipt.formation.code []) functions (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld ∧
  ∃ returned : callerProtocol.State ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates argumentState returned ∧
    PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) wordType outcome returned

include atHeader shape admitted argumentsTrace in
/-- The real call trace authenticates the final raw heap. The Carrier lift
returns its existing pool and does not run another physical restoration. -/
private theorem result_admission {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after)
    (result : CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.ResultAt (registry := registry) (faults := faults)
      (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] captured prefixContext)
      (receipt.formation.code []) functions (bridge.pool argumentState) outcome after value finalStore finalMap finalWorld) :
    ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState outcome after value finalStore finalMap finalWorld := by
  have actualCalled : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function []))
      [SourceCoreChosenOrdinaryAcceptedArgumentAdmission.argumentValue] outcome after := by
    simpa only [(arguments_at fixture argumentsTrace).1] using called
  have sourcePost := call_heap fixture atHeader shape receipt admitted.heap actualCalled
  have kept := result
  obtain ⟨_represented, _heaps, maps, worlds, frame, metadata, reached, related⟩ := result
  obtain ⟨returned, _samePool, returnedRelated⟩ := bridge.restore argumentState reached maps worlds frame metadata related
  refine ⟨kept, returned, returnedRelated, ?_⟩
  refine ⟨CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool argumentState) (bridge.pool returned) admitted.rows frame, ?_⟩
  intro sourceValue isValue
  have sameValue := Dynamic.ExpressionOutcome.value.inj (isValue.symm.trans sourcePost.1)
  cases sameValue
  exact ⟨.word _, sourcePost.2⟩

include atHeader shape typing chosen origin observed admitted heaps represented reference argumentsTrace sameNative selected in
/-- The real Source argument trace constructs raw typing at this argument
state. The literal application and original accepted fourth bind run once. -/
theorem application_preserves (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) size
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
        (LanguageResult.bind compiler.resultType
          (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧
      ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState
        outcome after value finalStore finalMap finalWorld := by
  have passed := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader receipt dispatch selected native.diagnostics.unknown).fourth
  have rawTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) middle arguments [parameterType] := by
    rw [(arguments_at fixture argumentsTrace).1]
    exact SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed _ _
  have beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) middle :=
    (Dynamic.HeapWellTyped.iff_of_binderExtends typing.extended).mpr admitted.heap
  obtain ⟨value, finalStore, finalMap, finalWorld, application, result⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralInvocation.application_preserves fixture atHeader receipt shape root chosen
      functions owner captured prefixContext history origin observed (bridge.pool argumentState) beforeTyped rawTyped
      admitted.rows represented heaps reference budget called within
  have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed] at gate
  rw [← sameNative] at application
  exact ⟨value, finalStore, finalMap, finalWorld,
    LanguageResult.bind_success compiler.resultType gate
      (CallableIndexedOwnedStoredApplicationProjection.evaluates_from_payload application),
    result_admission fixture atHeader shape receipt bridge functions captured prefixContext argumentState admitted
      argumentsTrace called result⟩

include atHeader shape typing chosen origin observed admitted heaps represented reference argumentsTrace sameNative selected in
/-- Genuine fourth-bind completion supplies its strict application child. The
selected literal continuation derives the body internally at this exact state. -/
theorem application_reflects (budget : Nat)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication native.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) sourceSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
        (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) arguments outcome after ∧
      ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions captured prefixContext argumentState
        outcome after value finalStore finalMap finalWorld := by
  have passed := (SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.accepted_at_selected
    fixture shape atHeader receipt dispatch selected native.diagnostics.unknown).fourth
  have rawTyped : Dynamic.ValuesHaveTypes (runtimeContext fixture.packet) middle arguments [parameterType] := by
    rw [(arguments_at fixture argumentsTrace).1]
    exact SourceCoreChosenOrdinaryAcceptedArgumentAdmission.arguments_typed _ _
  have beforeTyped : Dynamic.HeapWellTyped (runtimeContext fixture.packet) middle :=
    (Dynamic.HeapWellTyped.iff_of_binderExtends typing.extended).mpr admitted.heap
  have read : Evaluates (DataPatternValues.packValues payloads :: .unit :: calleeNative :: actual) argumentStore
      (.second (.var 2)) (.word dispatch.contract) argumentStore :=
    .second (.var (by simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have gate := prepared.site.dispatch_known .beforeApplication native.diagnostics.unknown
    dispatch.contract dispatch.row dispatch.found read
  rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication passed] at gate
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed failed _ =>
    have same := (evaluation_deterministic failed.sound gate).1
    cases same
  | continued acceptedGate applicationTrace _gateStrict applicationStrict =>
    obtain ⟨same, stores⟩ := evaluation_deterministic acceptedGate.sound gate
    cases same
    subst stores
    have payload := CallableIndexedOwnedStoredApplicationProjection.to_payload applicationTrace
    rw [sameNative] at payload
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
      SourceCoreChosenOrdinaryAcceptedLiteralInvocation.application_reflects fixture atHeader receipt shape root chosen
        functions owner captured prefixContext history origin observed (bridge.pool argumentState) beforeTyped rawTyped
        admitted.rows represented heaps reference budget payload (Nat.le_of_lt applicationStrict)
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called,
      result_admission fixture atHeader shape receipt bridge functions captured prefixContext argumentState admitted
        argumentsTrace called result⟩

end Current

section SuccessStep
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (profile : fixture.packet.compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {calleeMap : LocationMap} {calleeWorld : StoreTyping} {actualEnvironment : Environment}
    (captured : Captures fixture.packet.compiled.indexed calleeMap calleeWorld (initialScope fixture.packet)
      (receipt.formation.function []).captured actualEnvironment)
    (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
      (values := .initial fixture.packet.compiled.compatible.checked) caller)
    (history : History (receipt.formation.code []))
    (origin : SourceOrigin (receipt.formation.support []) history)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
    (reference : captured.canonical[(receipt.formation.code []).referenceIndex]? =
      some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {compilerFuel : Nat}
    {compilerContext : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
    {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body compilerFuel compilerContext
      (source fixture.packet.named) scope (expressionId fixture.packet 5) (expressionId fixture.packet 9)
      [expressionId fixture.packet 6] metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
    {sidecar : SourceCoreStageContracts.Sidecar} {calleeNative : Value} {actual : Environment} {ξ : Renaming}
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call
      [expressionId fixture.packet 6] (.closure (receipt.formation.function [])) calleeNative)
    (sameNative : calleeNative = CallableIndexedLambdaValues.value (receipt.formation.code [])
      captured.embedding history.native actualEnvironment)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site
      (expressionId fixture.packet 9) [expressionId fixture.packet 6] metadata compiler.original dispatch.row)
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      (receipt.formation.code []).receipt.parameterCore)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {firstMap : LocationMap} {firstWorld : StoreTyping} {before calleeHeap : Dynamic.Heap}
    {firstStore calleeStore : Store} {canonical : Environment}
    (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)

include atHeader shape typing chosen profile origin observed reference selected sameNative nativeBundle in
/-- The original whole successful prefix and fourth bind remain beside the
independent Source call and actual returned admission. No argument or body
meaning callback is supplied; the same step's values construct the bundle. -/
theorem reflects_success_step (budget : Nat) {value : Value} {finalStore : Store} {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      calleeSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 9)
      (.closure (receipt.formation.function [])) calleeHeap)
    (original : CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) bridge functions compiler prepared first budget value finalStore)
    (step : CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore)
    (passed : CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore) :
    CallableIndexedOwnedStoredIndirectArgumentPrefix.ForModel.SuccessPrefix
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.SuccessStep
      (registry := registry) (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (evidence := evidence) (environment := environment) (actual := actual) (ξ := ξ)
      (sourceTypes := [parameterType]) (calleeHeap := calleeHeap) (calleeNative := calleeNative)
      (calleeStore := calleeStore) (calleeMap := calleeMap) (calleeWorld := calleeWorld)
      bridge functions compiler prepared first budget value finalStore ∧
    CallableIndexedOwnedStoredIndirectApplicationPrefix.PassedAt (actual := actual)
      compiler prepared dispatch budget value finalStore ∧
    ∃ argumentsSize sources payloads middle argumentStore middleMap middleWorld,
    ∃ (stepMaps : LocationMap.Extends calleeMap middleMap) (stepWorlds : WorldExtends calleeWorld middleWorld)
      (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, argumentStore, canonical⟩),
      callerProtocol.Relates first argumentState ∧
      Admission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) argumentState ∧
      DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        middleMap middleWorld [parameterType] (compiler.codes.map (·.type)) sources payloads ∧
      SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked fixture.packet.compiled.sourceProgram) argumentsSize
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
        (source fixture.packet.named) environment calleeHeap [expressionId fixture.packet 6] sources middle ∧
      ∃ callSize outcome after finalMap finalWorld,
        RecursiveNamedCallBounds.CallOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram) callSize
          (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
          (receipt.formation.function []).evidence middle (.closure (receipt.formation.function [])) sources outcome after ∧
        ∃ parentSize, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
          parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence
          (source fixture.packet.named) environment before (expressionId fixture.packet 5) outcome after ∧
        ReturnedAt (registry := registry) (faults := faults) fixture receipt bridge functions
          (captured.extend stepMaps stepWorlds) prefixContext argumentState outcome after value finalStore finalMap finalWorld := by
  refine ⟨original, step, passed, ?_⟩
  obtain ⟨nativeSize, argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    _argumentsNative, _argumentsStrict, argumentsTrace, values, argumentHeaps, stepMaps, stepWorlds, _stepFrame, _stepMetadata,
    _maps, _worlds, _frame, _metadata, ⟨argumentState, related, admitted⟩,
    remainingSize, remaining, remainingStrict⟩ := step
  let current := captured.extend stepMaps stepWorlds
  have rawBundle : TypeSystem.Ty.productMany [parameterType] =
      TypeSystem.Ty.productMany ((receipt.formation.function []).parameters.map (fun binder => binder.scheme.body)) := by
    rw [(SourceCoreChosenOrdinaryAcceptedLiteralInvocation.support_shape fixture atHeader receipt []).1, shape.parameters]
    simp only [List.map_cons, List.map_nil, shape.scheme, TypeSystem.Scheme.mono]
  have count : (compiler.codes.map (·.type)).length = (receipt.formation.function []).parameters.length := by
    have physical := SourceCoreChosenOrdinaryAcceptedLiteralCallGuard.physical_arity fixture shape atHeader receipt
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans physical.symm
  have actualArguments := CallableIndexedOwnedPreparedOrdinaryLambdaInvocation.arguments_of_bundles
    (CallableIndexedOwnedChosenOrdinaryFormedMembers.capture_at receipt [] current prefixContext)
    (receipt.formation.code []) (receipt.formation.support []) (receipt.formation.prepared [])
    functions profile values (count.symm.trans values.length.1) rawBundle nativeBundle
  obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, result⟩ :=
    application_reflects (registry := registry) (faults := faults)
      (atHeader := atHeader) (shape := shape) (typing := typing) (receipt := receipt) (root := root) (chosen := chosen)
      (bridge := bridge) (functions := functions) (owner := owner) (captured := current)
      (prefixContext := prefixContext) (history := history) (origin := origin) (observed := observed)
      (argumentState := argumentState) (admitted := admitted) (heaps := argumentHeaps)
      (represented := actualArguments) (reference := reference) (argumentsTrace := argumentsTrace)
      (compiler := compiler) (prepared := prepared) (dispatch := dispatch) (sameNative := sameNative)
      (selected := selected) fixture budget remaining (Nat.le_of_lt remainingStrict)
  obtain ⟨parentSize, sourceParent⟩ := parent_source fixture receipt calleeTrace argumentsTrace called
  exact ⟨argumentsSize, arguments, payloads, middle, argumentStore, middleMap, middleWorld,
    stepMaps, stepWorlds, argumentState, related, admitted, values, argumentsTrace,
    callSize, outcome, after, finalMap, finalWorld, called, parentSize, sourceParent, result⟩

end SuccessStep
end Tests.SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication
