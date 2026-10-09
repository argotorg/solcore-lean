import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyBounds

/-! Finite Source constructors compose the same selected initializer, actual
allocation and parent outcome. Their genuine Source sizes are independent of
native completion sizes. Admission transports only the context of the same
reached state, retaining its heap, pool and every ordered row. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  {lowered : SourceCoreBasic.LoweredExpr}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
    fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
    (expressionId fixture.packet 1) lowered)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  {environment : Dynamic.Environment} {before allocated after : Dynamic.Heap}
  {location : Dynamic.Location}

include atHeader in
/-- The selected receipt supplies its actual pure initializer and a real
Source grade, without using a native execution or a body law. -/
theorem initializer_sized :
    ∃ size, SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.closure (receipt.formation.function environment)) before := by
  have trace := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_evaluates
    fixture environment atHeader receipt before
  rw [atHeader.named] at trace
  exact SourceExecutionSize.ExpressionEvaluates.has_size trace

private def bodySize (initializerSize parentSize : Nat) : Nat :=
  SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [initializerSize],
    SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [parentSize]]]

private theorem bodySize_children (initializerSize parentSize : Nat) :
    initializerSize < bodySize initializerSize parentSize ∧
      parentSize < bodySize initializerSize parentSize := by
  simp only [bodySize, SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
  omega

include typing in
private theorem initialized_head {initializerSize : Nat}
    (initializer : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.closure (receipt.formation.function environment)) before)
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function environment))) location allocated) :
    SourceExecutionSize.StatementExecutes (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceExecutionSize.stepSize [initializerSize]) (runtimeContext fixture.packet) []
      (source fixture.packet.named) environment before (statementId fixture.packet 0)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (.fallthrough ((fixture.graph.binder.id, location) :: environment)) allocated := by
  have mono : fixture.graph.binder.scheme.quantified = [] := by rw [typing.scheme]; rfl
  exact .letInitialized (lookupStatement?_sound fixture.graph.initializedFound)
    fixture.graph.initializedForm initializer mono typing.extended allocation

include atHeader typing in
/-- Actual successful parent execution returns through the two original
statements, retaining the allocated heap and exact selected Source closure. -/
theorem body_from_parent_value {parentSize : Nat} {value : Dynamic.Value}
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function environment))) location allocated)
    (parent : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) value after) :
    ∃ initializerSize wholeSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1) (.closure (receipt.formation.function environment)) before ∧
      SourceExecutionSize.FunctionStatementsExecute (Program.ofChecked fixture.packet.compiled.sourceProgram)
        wholeSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        [statementId fixture.packet 0, statementId fixture.packet 4]
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) (.returned value) after ∧
      initializerSize < wholeSize ∧ parentSize < wholeSize := by
  obtain ⟨initializerSize, initializer⟩ := initializer_sized fixture atHeader receipt (environment := environment) (before := before)
  have head := initialized_head fixture receipt typing initializer allocation
  have returned := SourceExecutionSize.StatementExecutes.returnValue
    (lookupStatement?_sound fixture.graph.outerReturnFound) fixture.graph.outerReturnForm parent
  have notTail : ∀ expression, fixture.graph.outerReturn.form ≠ .expression expression false := by
    intro expression
    rw [fixture.graph.outerReturnForm]
    intro same
    cases same
  have tail := SourceExecutionSize.FunctionStatementsExecute.singleton
    (lookupStatement?_sound fixture.graph.outerReturnFound) notTail returned
  exact ⟨initializerSize, bodySize initializerSize parentSize, initializer,
    .cons head tail, bodySize_children initializerSize parentSize⟩

include atHeader typing in
/-- A genuine parent fault follows the same successful initializer and
allocation. The original fault token and final Source heap are unchanged. -/
theorem body_from_parent_fault {parentSize : Nat} {reason : Dynamic.SemanticFault}
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function environment))) location allocated)
    (parent : SourceExecutionSize.ExpressionFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) reason after) :
    ∃ initializerSize wholeSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1) (.closure (receipt.formation.function environment)) before ∧
      SourceExecutionSize.FunctionStatementsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
        wholeSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        [statementId fixture.packet 0, statementId fixture.packet 4]
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) reason after ∧
      initializerSize < wholeSize ∧ parentSize < wholeSize := by
  obtain ⟨initializerSize, initializer⟩ := initializer_sized fixture atHeader receipt (environment := environment) (before := before)
  have head := initialized_head fixture receipt typing initializer allocation
  have returned := SourceExecutionSize.StatementFaults.returnValue
    (lookupStatement?_sound fixture.graph.outerReturnFound) fixture.graph.outerReturnForm parent
  have tail := SourceExecutionSize.FunctionStatementsFault.singleton returned
  exact ⟨initializerSize, bodySize initializerSize parentSize, initializer,
    .tail head tail, bodySize_children initializerSize parentSize⟩

include atHeader typing in
/-- The actual parent outcome selects one finite construction, preserving
both measured child grades and the literal returned context. -/
theorem body_from_parent {parentSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function environment))) location allocated)
    (parent : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) outcome after) :
    ∃ wholeSize, RecursiveNamedLoopContracts.ExecutesAt wholeSize true
      (Program.ofChecked fixture.packet.compiled.sourceProgram) (runtimeContext fixture.packet) []
      (source fixture.packet.named) environment before [statementId fixture.packet 0, statementId fixture.packet 4]
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      (match outcome with | .value value => .returned value | .fault reason => .fault reason) after ∧
      parentSize < wholeSize := by
  cases parent with
  | value parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_value fixture atHeader receipt typing allocation parent
    exact ⟨size, .control constructed, parentSmall⟩
  | fault parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_fault fixture atHeader receipt typing allocation parent
    exact ⟨size, .fault constructed, parentSmall⟩

include atHeader typing in
/-- The Header adapter uses its genuine Source/body/context equations. Its
empty evidence is explicit rather than inferred from emitted native code. -/
theorem body_trace_at_header {parentSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (evidence : caller.function.evidence = [])
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function environment))) location allocated)
    (parent : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) outcome after) :
    ∃ wholeSize, RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      wholeSize caller.function caller.context environment before outcome after ∧ parentSize < wholeSize := by
  cases parent with
  | value parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_value fixture atHeader receipt typing allocation parent
    refine ⟨size, .returned (finalContext := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) ?_, parentSmall⟩
    simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using constructed
  | fault parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_fault fixture atHeader receipt typing allocation parent
    refine ⟨size, .fault (finalContext := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) ?_, parentSmall⟩
    simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using constructed

section Admission
open CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {protocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
    {index : ProtectedStateTransition.Index} (reached : protocol.State index)

include typing in
/-- Only the Source context changes. The actual reached heap, pool and all
ordered rows remain the same; raw typing is transported by the real binder. -/
theorem post_admission_at_runtime {type : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (post : PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      type outcome reached) :
    PostAdmission bridge (runtimeContext fixture.packet) type outcome reached := by
  refine ⟨post.rows, ?_⟩
  intro value same
  obtain ⟨valueTyped, heapTyped⟩ := post.successful value same
  exact ⟨(Dynamic.ValueHasType.iff_of_binderExtends typing.extended).mpr valueTyped,
    (Dynamic.HeapWellTyped.iff_of_binderExtends typing.extended).mpr heapTyped⟩

end Admission
end Tests.SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction
