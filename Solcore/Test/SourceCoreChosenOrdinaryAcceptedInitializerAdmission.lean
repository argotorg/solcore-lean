import Solcore.Test.SourceCoreChosenOrdinaryAcceptedTyping
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedLiteralSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission

/-! The actual initializer lambda cannot fault: it copies the captured cells
and returns the closure over the copies. Its genuine raw closure typing and
initial admission retain every stable row. The chosen compiler receipt is
aligned through its original Source lookup. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open CallableIndexedOwnedOrdinaryLambdaSourceFacts CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture)

/-- This is the exact Source lambda at occurrence one, with its actual captures. -/
def initializer (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) : Dynamic.Closure :=
  closure fixture.packet.named fixture.graph.parameters wordType [statementId fixture.packet 2]
    (runtimeContext fixture.packet) evidence environment

variable (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment)

include shape in
/-- The genuine lambda judgment retains the actual raw function and body rows. -/
theorem source_facts : Facts (initializer fixture evidence environment)
    (expressionId fixture.packet 1) fixture.graph.lambdaNode := by
  exact of_typed fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
    fixture.graph.lambdaFound fixture.graph.lambdaForm
    (SourceCoreChosenOrdinaryAcceptedTyping.lambda_typed shape) fixture.graph.lambdaCoercions

include shape in
/-- Covering evidence and the actual captured environment close the static
closure code; no whole-program execution theorem is used. -/
theorem value_has_type {heap : Dynamic.Heap}
    (covers : evidence.Covers (runtimeContext fixture.packet))
    (captures : Dynamic.EnvironmentAgrees heap (runtimeContext fixture.packet).locals environment) :
    Dynamic.ValueHasType (runtimeContext fixture.packet) heap
      (.closure (initializer fixture evidence environment)) fixture.graph.lambdaNode.type := by
  have facts := source_facts fixture shape evidence environment
  have frame := facts.frame fixture.runtime.source_runtime covers
  rw [facts.sourceType]
  exact .closure rfl frame.code covers captures

/-- The literal lambda constructor yields a real Source execution that copies
the captured cells and returns the closure over the copies, independently of
its native compiler budget. -/
theorem evaluates {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.closure (initializer fixture evidence captured)) after := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound fixture.graph.lambdaFound)
  · rw [fixture.graph.lambdaForm]
    exact .lambda (by simp only [fixture.graph.lambdaRequirements, fixture.graph.lambdaCoercions]; rfl) snapshot
  · rw [fixture.graph.lambdaCoercions]
    exact .nil

private theorem value_of_facts {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {id : ExpressionId} {node : ExpressionNode} (facts : Facts function id node)
    (unique : NodeOccurrencesUnique function.source) {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : Dynamic.ExpressionEvaluates program function.context function.evidence
      function.source function.captured before id value after) :
    ∃ captured, value = .closure {function with captured := captured} ∧
      Dynamic.EnvironmentCopies function.source function.captured before captured after := by
  cases trace with
  | intro found raw coercions =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.coercions] at coercions
    cases coercions
    rw [facts.form] at raw
    cases raw with
    | lambda _ snapshot => exact ⟨_, rfl, snapshot⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at form
    cases form

private theorem fault_of_facts {program : SourceSemantics.Program} {function : Dynamic.Closure}
    {id : ExpressionId} {node : ExpressionNode} (facts : Facts function id node)
    (unique : NodeOccurrencesUnique function.source) {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionFaults program function.context function.evidence
      function.source function.captured before id reason after) : False := by
  cases trace with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent facts.contains
  | form found raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at raw
    cases raw
  | coercion found _ failed =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.coercions] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique found).symm.trans
      (lookupExpression?_complete unique facts.contains))
    subst same
    rw [facts.form] at form
    cases form

include shape in
/-- Any actual initializer value trace copies the captured cells and returns
this same closure over the copies, at the copied heap. -/
theorem values_at {program : SourceSemantics.Program} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (trace : Dynamic.ExpressionEvaluates program (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) value after) :
    ∃ captured, value = .closure (initializer fixture evidence captured) ∧
      Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after :=
  value_of_facts (source_facts fixture shape evidence environment)
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace

include shape in
/-- Ordinary lambda formation with its actual empty coercions cannot fault. -/
theorem no_fault {program : SourceSemantics.Program} {size : Nat} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (trace : SourceExecutionSize.ExpressionFaults program size (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) reason after) : False :=
  fault_of_facts (source_facts fixture shape evidence environment)
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique trace.sound

include shape in
/-- This retains the actual sized Source outcome without identifying its
size with the native lambda compiler or completion size. -/
theorem outcome_at {program : SourceSemantics.Program} {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size (runtimeContext fixture.packet) evidence
      (source fixture.packet.named) environment before (expressionId fixture.packet 1) outcome after) :
    ∃ captured, outcome = .value (.closure (initializer fixture evidence captured)) ∧
      Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after := by
  cases trace with
  | value trace =>
    obtain ⟨captured, rfl, copies⟩ := values_at fixture shape evidence environment trace.sound
    exact ⟨captured, rfl, copies⟩
  | fault trace => exact False.elim (no_fault fixture shape evidence environment trace)

/-- The Source producer itself supplies a genuine finite execution size. -/
theorem has_size {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) evidence (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.value (.closure (initializer fixture evidence captured))) after :=
  RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value (evaluates fixture evidence environment snapshot))

section Admission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {protocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
    {index : ProtectedStateTransition.Index} (initial : protocol.State index)

include shape in
/-- The closure over an environment that agrees with this actual state is
admitted at it. Its deep heap typing and every row's own stable history come
from the initial admission. -/
theorem post_admission
    (covers : evidence.Covers (runtimeContext fixture.packet))
    (captures : Dynamic.EnvironmentAgrees index.heap (runtimeContext fixture.packet).locals environment)
    (admitted : Admission bridge (runtimeContext fixture.packet) initial) :
    PostAdmission bridge (runtimeContext fixture.packet) fixture.graph.lambdaNode.type
      (.value (.closure (initializer fixture evidence environment))) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨value_has_type fixture shape evidence environment covers captures, admitted.heap⟩

end Admission

section ActualReceipt
open CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
variable {caller : ActualHeader fixture} (atHeader : HeaderAt fixture caller)
    {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : Compilation fixture.packet.compiled.indexed caller.named
      (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
    (receipt : Receipt caller (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics)
      fixture.packet.namedCode compilation (runtimeContext fixture.packet) [] (initialScope fixture.packet)
      (expressionId fixture.packet 1) lowered)

include atHeader in
/-- Original lookup and Header identity align the actual selected receipt's
closure, including its captures. There is no representation inverse. -/
theorem receipt_function : receipt.formation.function environment = initializer fixture [] environment := by
  obtain ⟨parameters, result, statements⟩ :=
    SourceCoreChosenOrdinaryAcceptedLiteralSupport.produced_shape fixture atHeader receipt.formation.produced
  change closure caller.named _ _ _ (runtimeContext fixture.packet) [] environment = _
  rw [parameters, result, statements, atHeader.named]
  rfl

include atHeader shape in
/-- Raw Source typing is attached to the same actual selected function. -/
theorem receipt_value_has_type {heap : Dynamic.Heap}
    (captures : Dynamic.EnvironmentAgrees heap (runtimeContext fixture.packet).locals environment) :
    Dynamic.ValueHasType (runtimeContext fixture.packet) heap
      (.closure (receipt.formation.function environment)) fixture.graph.lambdaNode.type := by
  rw [receipt_function fixture environment atHeader receipt]
  exact value_has_type fixture shape [] environment
    (receipt.formation.support environment).body.frame.evidence_covers captures

include atHeader shape in
/-- The selected receipt has the same initializer outcome: the closure over the
copies, at the copied heap. -/
theorem receipt_outcome_at {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) [] (source caller.named) environment before
      (expressionId fixture.packet 1) outcome after) :
    ∃ captured, outcome = .value (.closure (receipt.formation.function captured)) ∧
      Dynamic.EnvironmentCopies (source caller.named) environment before captured after := by
  have original := trace
  rw [atHeader.named] at original
  obtain ⟨captured, sameValue, copies⟩ := outcome_at fixture shape [] environment original
  rw [← receipt_function fixture captured atHeader receipt] at sameValue
  rw [atHeader.named]
  exact ⟨captured, sameValue, copies⟩

include atHeader in
/-- The same selected receipt has a genuine initializer Source execution over
the copies of its captured cells. -/
theorem receipt_evaluates {before after : Dynamic.Heap} {captured : Dynamic.Environment}
    (snapshot : Dynamic.EnvironmentCopies (source caller.named) environment before captured after) :
    Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (runtimeContext fixture.packet) [] (source caller.named) environment before
      (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) after := by
  rw [receipt_function fixture captured atHeader receipt, atHeader.named]
  rw [atHeader.named] at snapshot
  exact evaluates fixture [] environment snapshot

section ReceiptAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {protocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
    {index : ProtectedStateTransition.Index} (initial : protocol.State index)

include atHeader shape in
/-- Covering evidence comes from the actual recaptured static frame. The raw
closure and success admission refer to this same receipt and initial state. -/
theorem receipt_post_admission
    (captures : Dynamic.EnvironmentAgrees index.heap (runtimeContext fixture.packet).locals environment)
    (admitted : Admission bridge (runtimeContext fixture.packet) initial) :
    PostAdmission bridge (runtimeContext fixture.packet) fixture.graph.lambdaNode.type
      (.value (.closure (receipt.formation.function environment))) initial := by
  refine ⟨admitted.rows, ?_⟩
  intro value same
  cases same
  exact ⟨receipt_value_has_type fixture shape environment atHeader receipt captures, admitted.heap⟩

end ReceiptAdmission

end ActualReceipt
end Tests.SourceCoreChosenOrdinaryAcceptedInitializerAdmission
