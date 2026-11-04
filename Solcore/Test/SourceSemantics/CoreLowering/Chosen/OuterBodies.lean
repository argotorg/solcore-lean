import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Bodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
import Solcore.Test.SourceSemantics.CoreLowering.Chosen.Admission
import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts

/-!
# Chosen ordinary outer body tests

Outer bounds and state correspondence of the accepted ordinary call, its lexical exits, parameter entry
and public body correspondence.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyBounds
/-! Finite ports for the actual accepted outer body retain the initializer,
marked allocation and return at their original states. Native inversion keeps
the actual parent child budget; Source inversion keeps its independent grade.
These ports supply the body composition without an assumed body meaning. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CoreProof CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (receipt : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)

/-- The hidden initializer payload and lexical reference keep their actual
positions in the emitted return expression. -/
theorem flow_rename (ξ : Renaming) :
    (SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.emittedFlow fixture receipt.annotation.expression).rename ξ =
      LanguageResult.bind (LocalLoop.controlType fixture.packet.named.signature.resultType)
        (fixture.calls.initializer.expression.rename ξ)
        (.letE (receipt.annotation.expression.rename ξ.lift)
          (LocalLoop.returnValue fixture.packet.named.signature.resultType
            (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) ξ).lift))) := by
  unfold SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.emittedFlow
    SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.returned
  rw [TypedLexicalControl.sequence_rename, LoopRenaming.returnValue]

include atHeader in
/-- The retained actual Header body has exactly this original finish helper. -/
theorem body_rename (ξ : Renaming) :
    caller.body.rename ξ = CompatibleStatements.finish fixture.packet.named.signature.resultType
      ((SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.emittedFlow fixture receipt.annotation.expression).rename ξ)
      fixture.calls.own.fellThroughReason fixture.calls.own.table.escapedReason := by
  rw [(SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.emitted_at_header fixture atHeader receipt).1,
    ImperativeFunctionFinish.rename]

variable {actual : Environment} {before allocated finalStore : Store} {ξ : Renaming}
  {closure reference value : Value}
  (initializer : Evaluates actual before (fixture.calls.initializer.expression.rename ξ)
    (.inRight .word closure) before)
  (allocation : Evaluates (closure :: actual) before (receipt.annotation.expression.rename ξ.lift)
    reference allocated)

include atHeader initializer allocation in
/-- An actual successful parent runs under the same allocation's reference
and hidden initializer payload, then returns through the original finish. -/
theorem whole_from_parent_value
    (parent : Evaluates (reference :: closure :: actual) allocated
      (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)
      (.inRight .word value) finalStore) :
    Evaluates actual before (caller.body.rename ξ) (.inRight .word value) finalStore := by
  rw [body_rename fixture atHeader receipt]
  apply LocalControl.finish_returned
  apply LocalLoop.toControl_normal
  rw [flow_rename fixture receipt]
  exact LanguageResult.bind_success _ initializer (.letE allocation (LocalLoop.returnValue_success _ parent))

include atHeader initializer allocation in
/-- A language fault from the actual parent keeps its final store and token
through the same initialized let, return and finish. -/
theorem whole_from_parent_fault {reason : Word}
    (parent : Evaluates (reference :: closure :: actual) allocated
      (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)
      (.inLeft fixture.packet.named.signature.resultType (.word reason)) finalStore) :
    Evaluates actual before (caller.body.rename ξ)
      (.inLeft fixture.packet.named.signature.resultType (.word reason)) finalStore := by
  rw [body_rename fixture atHeader receipt]
  apply LocalControl.finish_failure
  apply LocalLoop.toControl_failure
  rw [flow_rename fixture receipt]
  exact LanguageResult.bind_success _ initializer (.letE allocation (LocalLoop.returnValue_failure _ parent))

include atHeader initializer allocation in
/-- Whole completion contains the genuine parent child at the exact reached
allocation tuple. No replacement native derivation supplies its budget. -/
theorem parent_at_whole_completion {size : Nat} {result : Value}
    (completed : EvaluationSize size actual before (caller.body.rename ξ) result finalStore) :
    ∃ child parentResult parentStore, child < size ∧
      EvaluationSize child (reference :: closure :: actual) allocated
        (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)
        parentResult parentStore := by
  rw [body_rename fixture atHeader receipt] at completed
  obtain ⟨flowSize, _flowResult, _flowStore, flowSmall, flow⟩ :=
    RecursiveNamedCallBounds.finish_flow completed
  rw [flow_rename fixture receipt] at flow
  obtain ⟨branchSize, branchSmall, branch⟩ := flow.bind_success initializer
  obtain ⟨returnSize, returnSmall, returned⟩ := branch.let_body allocation
  obtain ⟨parentSize, parentStore, parentResult, parentSmall, parent⟩ := returned.bind_computation
  exact ⟨parentSize, parentResult, parentStore,
    Nat.lt_trans parentSmall (Nat.lt_trans returnSmall (Nat.lt_trans branchSmall flowSmall)), parent⟩

include atHeader initializer allocation in
/-- The authentic parent child can use the whole completion's budget. -/
theorem parent_within_whole_budget (budget : Nat) {size : Nat} {result : Value}
    (completed : EvaluationSize size actual before (caller.body.rename ξ) result finalStore)
    (within : size ≤ budget) :
    ∃ child parentResult parentStore, child ≤ budget ∧
      EvaluationSize child (reference :: closure :: actual) allocated
        (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) ξ).lift)
        parentResult parentStore := by
  obtain ⟨child, parentResult, parentStore, smaller, parent⟩ :=
    parent_at_whole_completion fixture atHeader receipt initializer allocation completed
  exact ⟨child, parentResult, parentStore, Nat.le_trans (Nat.le_of_lt smaller) within, parent⟩

/-- Finite Source inversion retains the original initializer, which copies the
captured cells and forms the closure over the copies, the actual Source
allocation at the copied heap and the parent outcome, including faults after
the successful let. -/
theorem source_parent_at_body
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {control : Dynamic.ControlOutcome}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true
      (Program.ofChecked fixture.packet.compiled.sourceProgram) (runtimeContext fixture.packet) []
      (source fixture.packet.named) environment before
      [statementId fixture.packet 0, statementId fixture.packet 4] finalContext control after) :
    finalContext = SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture ∧
    ∃ initializerSize parentSize captured copied location middle outcome,
      Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied ∧
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1)
        (.closure (SourceCoreChosenOrdinaryAcceptedInitializerAdmission.initializer fixture [] captured)) copied ∧
      Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
        (some (.closure (SourceCoreChosenOrdinaryAcceptedInitializerAdmission.initializer fixture [] captured))) location middle ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
        (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) middle
        (expressionId fixture.packet 5) outcome after ∧
      control = (match outcome with | .value value => .returned value | .fault reason => .fault reason) ∧
      initializerSize < size ∧ parentSize < size := by
  have mono : fixture.graph.binder.scheme.quantified = [] := by rw [typing.scheme]; rfl
  have original := RecursiveNamedLexicalTreeSourceBounds.initialized
    fixture.runtime.source_runtime.graph.nodeOccurrencesUnique fixture.graph.initializedFound
    fixture.graph.initializedForm mono typing.extended trace
  rcases original with failed | completed
  · obtain ⟨child, _reason, _context, _control, fault, _smaller⟩ := failed
    exact False.elim (SourceCoreChosenOrdinaryAcceptedInitializerAdmission.no_fault fixture shape [] environment fault)
  · obtain ⟨child, tailSize, sourceValue, location, copied, allocatedHeap, evaluated, allocated, tail,
      childSmall, tailSmall⟩ := completed
    obtain ⟨captured, valueEq, copies⟩ := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.values_at
      fixture shape [] environment evaluated.sound
    subst sourceValue
    obtain ⟨contextEq, parentSize, outcome, parent, controlEq, parentSmall⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.returning fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
        fixture.graph.outerReturnFound fixture.graph.outerReturnForm tail
    exact ⟨contextEq, child, parentSize, captured, copied, location, allocatedHeap, outcome, copies, evaluated,
      allocated, parent, controlEq, childSmall, Nat.lt_trans parentSmall tailSmall⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction
/-! Finite Source constructors compose the same selected initializer, which
copies the captured cells and forms the closure over the copies, the actual
allocation at the copied heap and the parent outcome. Their genuine Source
sizes are independent of native completion sizes. Admission transports only
the context of the same reached state, retaining its heap, pool and every
ordered row. -/
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
  {environment captured : Dynamic.Environment} {before copied allocated after : Dynamic.Heap}
  {location : Dynamic.Location}

include atHeader in
/-- The selected receipt supplies its actual initializer over the copies of
the captured cells and a real Source grade, without using a native execution
or a body law. -/
theorem initializer_sized
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied) :
    ∃ size, SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
      (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) copied := by
  have trace := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_evaluates
    fixture environment atHeader receipt (by rw [atHeader.named]; exact snapshot)
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
      (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) copied)
    (allocation : Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function captured))) location allocated) :
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
statements, retaining the allocated heap and exact selected Source closure over
the copies. -/
theorem body_from_parent_value {parentSize : Nat} {value : Dynamic.Value}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied)
    (allocation : Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function captured))) location allocated)
    (parent : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) value after) :
    ∃ initializerSize wholeSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) copied ∧
      SourceExecutionSize.FunctionStatementsExecute (Program.ofChecked fixture.packet.compiled.sourceProgram)
        wholeSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        [statementId fixture.packet 0, statementId fixture.packet 4]
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) (.returned value) after ∧
      initializerSize < wholeSize ∧ parentSize < wholeSize := by
  obtain ⟨initializerSize, initializer⟩ := initializer_sized fixture atHeader receipt snapshot
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
/-- A genuine parent fault follows the same successful initializer over the
copies and allocation. The original fault token and final Source heap are
unchanged. -/
theorem body_from_parent_fault {parentSize : Nat} {reason : Dynamic.SemanticFault}
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied)
    (allocation : Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function captured))) location allocated)
    (parent : SourceExecutionSize.ExpressionFaults (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) reason after) :
    ∃ initializerSize wholeSize,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1) (.closure (receipt.formation.function captured)) copied ∧
      SourceExecutionSize.FunctionStatementsFault (Program.ofChecked fixture.packet.compiled.sourceProgram)
        wholeSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        [statementId fixture.packet 0, statementId fixture.packet 4]
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) reason after ∧
      initializerSize < wholeSize ∧ parentSize < wholeSize := by
  obtain ⟨initializerSize, initializer⟩ := initializer_sized fixture atHeader receipt snapshot
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
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied)
    (allocation : Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function captured))) location allocated)
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
      body_from_parent_value fixture atHeader receipt typing snapshot allocation parent
    exact ⟨size, .control constructed, parentSmall⟩
  | fault parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_fault fixture atHeader receipt typing snapshot allocation parent
    exact ⟨size, .fault constructed, parentSmall⟩

include atHeader typing in
/-- The Header adapter uses its genuine Source/body/context equations. Its
empty evidence is explicit rather than inferred from emitted native code. -/
theorem body_trace_at_header {parentSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (evidence : caller.function.evidence = [])
    (snapshot : Dynamic.EnvironmentCopies (source fixture.packet.named) environment before captured copied)
    (allocation : Dynamic.Heap.Allocates copied fixture.graph.binder.scheme.body
      (some (.closure (receipt.formation.function captured))) location allocated)
    (parent : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) ((fixture.graph.binder.id, location) :: environment) allocated
      (expressionId fixture.packet 5) outcome after) :
    ∃ wholeSize, RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      wholeSize caller.function caller.context environment before outcome after ∧ parentSize < wholeSize := by
  cases parent with
  | value parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_value fixture atHeader receipt typing snapshot allocation parent
    refine ⟨size, .returned (finalContext := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) ?_, parentSmall⟩
    simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using constructed
  | fault parent =>
    obtain ⟨_initializerSize, size, _initializer, constructed, _smaller, parentSmall⟩ :=
      body_from_parent_fault fixture atHeader receipt typing snapshot allocation parent
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds
/-! The accepted outer body uses one original formation and one initialized
allocation. Its parent executes at that same admitted post. Complete value and
fault results retain cumulative effects and the actual restored caller pool.
Reflection constructs an independent Source body from the genuine native child
and uses whole-body determinism to identify its final value and store. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)

include atHeader shape typing in
/-- The original body grade contains the actual parent outcome and Source
allocation. Other function control outcomes are excluded by the two statements. -/
theorem source_parent_at_body (evidence : caller.function.evidence = [])
    {size : Nat} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context [] before outcome after) :
    ∃ parentSize location allocated,
      Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
        (some (.closure (chosen.chosen.formation.function []))) location allocated ∧
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
        parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
        (source fixture.packet.named) [(fixture.graph.binder.id, location)] allocated
        (expressionId fixture.packet 5) outcome after ∧ parentSize < size := by
  have invert {finalContext control} (body : RecursiveNamedLoopContracts.ExecutesAt size true
      (Program.ofChecked fixture.packet.compiled.sourceProgram) (runtimeContext fixture.packet) []
      (source fixture.packet.named) [] before [statementId fixture.packet 0, statementId fixture.packet 4]
      finalContext control after) := SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.source_parent_at_body
        fixture shape typing body
  have closureEq := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.receipt_function
    fixture [] atHeader chosen.chosen
  cases trace with
  | returned trace =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .control (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, parentSize, _captured, _copied, location, allocated, parentOutcome, copies,
      _initializer, allocation, parent, sameControl, _initializerSmall, parentSmall⟩ := invert body
    cases copies
    rw [← closureEq] at allocation
    cases parentOutcome with
    | value value => cases sameControl; exact ⟨parentSize, location, allocated, allocation, parent, parentSmall⟩
    | fault _ => cases sameControl
  | fault trace =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .fault (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, parentSize, _captured, _copied, location, allocated, parentOutcome, copies,
      _initializer, allocation, parent, sameControl, _initializerSmall, parentSmall⟩ := invert body
    cases copies
    rw [← closureEq] at allocation
    cases parentOutcome with
    | value _ => cases sameControl
    | fault reason => cases sameControl; exact ⟨parentSize, location, allocated, allocation, parent, parentSmall⟩
  | unit same _ => rw [typing.header_result atHeader] at same; cases same
  | escaped trace escape =>
    have body : RecursiveNamedLoopContracts.ExecutesAt size true _ _ _ _ _ _ _ _ _ _ :=
      .control (by simpa only [atHeader.context, atHeader.source, atHeader.statements, evidence] using trace)
    obtain ⟨_, _initializerSize, _parentSize, _captured, _copied, _location, _allocated, parentOutcome, _copies,
      _initializer, _allocation, _parent, sameControl, _initializerSmall, _parentSmall⟩ := invert body
    rcases escape with ⟨_, same⟩ | ⟨_, same⟩ <;> cases parentOutcome <;> rw [same] at sameControl <;> cases sameControl

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {canonical : Environment} {before : Dynamic.Heap} {store : Store}
  {contextLocation : Location} {native : NativeFrame}
  (initial : State headers keys ⟨initialScope fixture.packet, mapping, world, before, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "first" => (⟨initial, packet⟩ : (protocol).State _)

/-- The complete body result refers to its actual restored caller and all
rows. Successful outcomes also retain raw Source value and deep heap typing. -/
def BodyResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents model finalMap finalWorld caller.function.resultType caller.output faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : (protocol).State ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩,
    (protocol).Relates first returned ∧ PostAdmission bridge (runtimeContext fixture.packet) caller.function.resultType outcome returned

include atHeader outer in
private theorem whole_of_parent {allocatedStore finalStore : Store} {reference closure result : Value}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {outcome : Dynamic.ExpressionOutcome}
    (initializer : Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding)
      (.inRight .word closure) store)
    (allocation : Evaluates (closure :: actual) store (outer.annotation.expression.rename captured.embedding.lift)
      reference allocatedStore)
    (parent : Evaluates (reference :: closure :: actual) allocatedStore
      (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) result finalStore)
    (represented : FunctionCalls.ResultRepresents model finalMap finalWorld chosen.parent.compiler.original.type
      fixture.calls.parent.type faults outcome result) :
    Evaluates actual store (caller.body.rename captured.embedding) result finalStore := by
  have nativeType := outer.parentType
  rw [nativeType] at represented
  cases represented with
  | value _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_value
      fixture atHeader outer initializer allocation parent
  | fault _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_fault
      fixture atHeader outer initializer allocation parent

include atHeader typing outer in
/-- Scope restoration keeps the parent's actual pool. Cumulative effects and
raw admission are transported from that same returned witness. -/
private theorem body_post_of_parent {allocatedMap finalMap : LocationMap} {allocatedWorld finalWorld : StoreTyping}
    {allocated after : Dynamic.Heap} {allocatedStore finalStore : Store} {reference result : Value}
    {outcome : Dynamic.ExpressionOutcome}
    (reached : (protocol).State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture,
      allocatedMap, allocatedWorld, allocated, allocatedStore, reference :: canonical⟩)
    (related : (protocol).Relates first reached)
    (maps : LocationMap.Extends mapping allocatedMap) (worlds : WorldExtends world allocatedWorld)
    (frame : AdministrativePreserved mapping store allocatedMap allocatedStore)
    (metadata : Dynamic.HeapMetadataExtend before allocated)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt
      (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) (registry := registry) (faults := faults)
      bridge functions chosen.parent.compiler reached outcome after result finalStore finalMap finalWorld) :
    BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
      (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, returnedRelated, admitted⟩ := post
  have rawType : chosen.parent.compiler.original.type = caller.function.resultType := by
    rw [chosen.parent.original, fixture.graph.parentType, typing.header_result atHeader]
  have nativeType : fixture.calls.parent.type = caller.output := outer.parentType.trans (by simpa only [atHeader.named] using caller.resultType)
  have runtimeAdmission := SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.post_admission_at_runtime
    fixture typing bridge returned admitted
  let restored := (CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner caller).restore (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
  refine ⟨?_, heaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
    metadata.trans finalMetadata, restored, ?_, ?_⟩
  · simpa only [rawType, nativeType] using represented
  · have restoredRelated : (protocol).Relates returned restored :=
      (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_related
        (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
    exact (protocol).trans related ((protocol).trans returnedRelated restoredRelated)
  · refine ⟨runtimeAdmission.rows, ?_⟩
    intro value same
    simpa only [rawType] using runtimeAdmission.successful value same

variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
    (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
  (stored : RuntimeStoreHasTypes world store fixture.packet.compiled.indexed.layouts.definitions)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (initialScope fixture.packet) [] canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      headers keys registry faults inventory.contracts) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (runtimeContext fixture.packet).locals [])
  (agrees : EnvironmentsAgree captured.embedding canonical actual)
  (reference : canonical[(initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
    some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type contextLocation))
  (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode fixture.packet.compiled.indexed.ancestry.layout.frame native))
  (ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
        headers keys registry faults inventory.contracts))).Ready ⟨initial, packet⟩ contextLocation native)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)) (runtimeContext fixture.packet) ⟨initial, packet⟩)

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- The genuine complete Source body constructs its initialized parent entry
once and preserves its actual whole result, effects and restored admission. -/
theorem preserves_body (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context [] before outcome after) (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (caller.body.rename captured.embedding) result finalStore ∧
      BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨parentSize, location, allocated, allocatedSource, parentTrace, parentSmall⟩ :=
    source_parent_at_body fixture atHeader shape typing root chosen evidence trace
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, location)] fixture.graph.binder.id location := .head
  obtain ⟨result, finalStore, finalMap, finalWorld, parent, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentPreservationBounds.preserves_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      _ [] extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup reached
      parentAdmission budget parentTrace (Nat.le_trans (Nat.le_of_lt parentSmall) within)
  exact ⟨result, finalStore, finalMap, finalWorld,
    whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured) initializer allocation parent post.1,
    body_post_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata post⟩

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- Native completion constructs its Source allocation and body independently.
The authentic child budget is retained; whole determinism aligns its final post. -/
theorem reflects_body (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (caller.body.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context [] before outcome after ∧
      BodyResultAt (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := by
  have allocatedSource : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (chosen.chosen.formation.function []))) _ _ := .append
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  obtain ⟨parentSize, parentResult, parentStore, parentWithin, parent⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.parent_within_whole_budget fixture atHeader outer initializer allocation
      budget completed within
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, ⟨before.cells.length⟩)]
      fixture.graph.binder.id ⟨before.cells.length⟩ := .head
  obtain ⟨parentSourceSize, outcome, after, finalMap, finalWorld, parentTrace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentReflectionBounds.reflects_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      reached extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup parentAdmission
      budget parent parentWithin
  have whole := whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured)
    initializer allocation parent.sound post.1
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic whole completed.sound
  subst result
  subst finalStore
  obtain ⟨sourceSize, sourceBody, _sourceParentSmall⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.body_trace_at_header fixture atHeader chosen.chosen typing
      evidence (.nil before) allocatedSource parentTrace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceBody,
    body_post_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata post⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
/-! The proved accepted body runs at the original named parameter receipt.
Its captures, native state, readiness and Source admission come from that same
BodyState. The public invocation ports retain its actual reached pool and all
returned rows, without a body execution law or whole-program typing premise. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (runtime : SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence.RuntimeEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
  (prefixZero : owner.key.capturePrefix = 0)
  {index : ProtectedStateTransition.Index} {argumentsPool : State headers keys index}
  {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    owner argumentsPool caller arguments)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "baseBridge" => CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

/-- Only the proof of the empty Source environment is transported. Every
native capture field comes from the original actual parameter BodyState. -/
def creation_capture : Captures fixture.packet.compiled.indexed receipt.body.mapping receipt.body.world
    (initialScope fixture.packet) (chosen.chosen.formation.function []).captured receipt.body.actualBody := by
  let captured := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry
    fixture functions owner receipt complete prefixZero runtime.globals
  exact {
    administrative := captured.administrative
    canonical := captured.canonical
    actualContext := captured.actualContext
    embedding := captured.embedding
    represented := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
        (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1,
        CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure]
        using captured.represented
    agrees := captured.agrees
    respects := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using captured.respects
    typed := captured.typed }

include runtime prefixZero in
/-- The packet and the pool are those of the same original receipt. -/
theorem input_packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
    ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
      receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ receipt.reached := by
  let original := receipt.packet prefixZero runtime.globals
  refine ⟨?_, ?_, ?_, original.carried⟩
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.globals
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.reference
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.bundle

/-- The complete actual body post retains its returned original pool and
successful raw value/heap typing, as well as all native cumulative effects. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents model finalMap finalWorld caller.function.resultType caller.output faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends receipt.body.mapping finalMap ∧ WorldExtends receipt.body.world finalWorld ∧
  AdministrativePreserved receipt.body.mapping receipt.body.store finalMap finalStore ∧
  Dynamic.HeapMetadataExtend receipt.body.heap after ∧
  ∃ returned : State headers keys ⟨caller.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      finalMap, finalWorld, after, finalStore, receipt.body.canonical⟩,
    Relates receipt.reached returned ∧ PostAdmission baseBridge caller.context caller.function.resultType outcome returned

include runtime prefixZero in
private theorem post_at_receipt {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.BodyResultAt
      (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
      (owner := owner) (canonical := receipt.body.canonical) (initial := receipt.reached) (packet := input_packet fixture runtime inventory root owner prefixZero receipt)
      outcome after value finalStore finalMap finalWorld) :
    ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, maps, worlds, frame, metadata, returned, related, admitted⟩ := post
  refine ⟨represented, heaps, maps, worlds, frame, metadata, returned.val, related, ?_⟩
  refine ⟨admitted.rows, ?_⟩
  intro sourceValue same
  simpa only [runtime.toHeaderAt.context] using admitted.successful sourceValue same

variable (extension : SourceCoreRawMetadata.Extends
  (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Apply the proved body once at the real parameter receipt, deriving every
capture, frame, readiness and admission port from that same actual input. -/
theorem preserves_at_receipt (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context receipt.body.environment receipt.body.heap outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (caller.body.rename receipt.body.embedding) value finalStore ∧
      ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  have originalTrace := trace
  rw [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at originalTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.preserves_body fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension
      observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence budget originalTrace within
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, post_at_receipt fixture runtime inventory root owner prefixZero receipt post⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The genuine native body child reflects to an independent Source grade at
that same parameter state; no Source body execution is supplied as an input. -/
theorem reflects_at_receipt (budget : Nat) {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context receipt.body.environment receipt.body.heap outcome after ∧
      ResultAt (fixture := fixture) (inventory := inventory) (root := root) (owner := owner) (receipt := receipt) outcome after value finalStore finalMap finalWorld := by
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.reflects_body fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension
      observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence budget completed within
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, post_at_receipt fixture runtime inventory root owner prefixZero receipt post⟩
  simpa only [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] using trace

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The existing Source invocation interface is satisfied at the actual receipt. -/
theorem source_body_at (size : Nat) :
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, returned, related, _admitted⟩ :=
    preserves_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete prefixZero receipt extension size trace (Nat.le_refl size)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, returned, related⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- The existing native invocation interface retains the independent Source cost. -/
theorem native_body_at (size : Nat) :
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, returned, related, _admitted⟩ :=
    reflects_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete prefixZero receipt extension size completed (Nat.le_refl size)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, returned, related⟩

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit
/-! The accepted initialized body retains its actual lexical stopping context
alongside the same represented result and returned admission. One original
initializer formation and allocation lead to one parent execution. The lexical
environment uses the supplied body's full administrative context. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (atHeader : HeaderAt fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
  (captured : Captures fixture.packet.compiled.indexed mapping world (initialScope fixture.packet)
    (chosen.chosen.formation.function []).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial fixture.packet.compiled.compatible.checked) caller)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {administrative : Core.Context} {canonical : Environment} {before : Dynamic.Heap} {store : Store}
  {contextLocation : Location} {native : NativeFrame}
  (initial : State headers keys ⟨initialScope fixture.packet, mapping, world, before, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "first" => (⟨initial, packet⟩ : (protocol).State _)

/-- The original body result and its actual lexical exit share every final index. -/
def BodyResultWithExit (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.BodyResultAt
    (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
    (owner := owner) (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld ∧
  TypedMixedNamedBody.ReachedExit fixture.packet.compiled.compatible.checked
    fixture.packet.compiled.indexed.layouts.definitions finalMap finalWorld administrative
    (Program.ofChecked fixture.packet.compiled.sourceProgram) caller.function caller.context
    (initialScope fixture.packet) [] before after outcome

/-- Forgetting the lexical component retains the original returned witness. -/
theorem BodyResultWithExit.forget {outcome after result finalStore finalMap finalWorld}
    (post : BodyResultWithExit (fixture := fixture) (inventory := inventory) (root := root)
      (registry := registry) (faults := faults) (owner := owner) (initial := initial) (packet := packet)
      (administrative := administrative) outcome after result finalStore finalMap finalWorld) :
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.BodyResultAt
      (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
      (owner := owner) (initial := initial) (packet := packet) outcome after result finalStore finalMap finalWorld := post.1

include typing in
/-- The binder genuinely reached after initialization remains represented at
its exact final map and world, including the supplied administrative suffix. -/
theorem lexical_at_parent {allocatedMap finalMap : LocationMap} {allocatedWorld finalWorld : StoreTyping}
    {allocated after : Dynamic.Heap} {location : Dynamic.Location} {reference : Value}
    (parentEnvironments : DataHeap.EnvRepresents
      (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      allocatedMap allocatedWorld administrative
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [(fixture.graph.binder.id, location)] (reference :: canonical)
      fixture.packet.compiled.indexed.layouts.definitions)
    (parentLocals : Dynamic.EnvironmentAgrees allocated
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals [(fixture.graph.binder.id, location)])
    (maps : LocationMap.Extends allocatedMap finalMap) (worlds : WorldExtends allocatedWorld finalWorld)
    (metadata : Dynamic.HeapMetadataExtend allocated after) :
    TypedStatementMixed.LexicalResult fixture.packet.compiled.compatible.checked
      fixture.packet.compiled.indexed.layouts.definitions finalMap finalWorld administrative
      (source fixture.packet.named).owner (runtimeContext fixture.packet)
      (initialScope fixture.packet) [] (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) after := by
  exact ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture,
    [(fixture.graph.binder.id, location)], reference :: canonical, .bind typing.extended .here,
    parentEnvironments.extend maps worlds, Dynamic.EnvironmentAgrees.mono metadata parentLocals⟩

include atHeader outer in
private theorem whole_of_parent {allocatedStore finalStore : Store} {reference closure result : Value}
    {finalMap : LocationMap} {finalWorld : StoreTyping} {outcome : Dynamic.ExpressionOutcome}
    (initializer : Evaluates actual store (fixture.calls.initializer.expression.rename captured.embedding)
      (.inRight .word closure) store)
    (allocation : Evaluates (closure :: actual) store (outer.annotation.expression.rename captured.embedding.lift)
      reference allocatedStore)
    (parent : Evaluates (reference :: closure :: actual) allocatedStore
      (fixture.calls.parent.expression.rename (Renaming.comp (Renaming.insertion 0) captured.embedding).lift) result finalStore)
    (represented : FunctionCalls.ResultRepresents model finalMap finalWorld chosen.parent.compiler.original.type
      fixture.calls.parent.type faults outcome result) :
    Evaluates actual store (caller.body.rename captured.embedding) result finalStore := by
  have nativeType := outer.parentType
  rw [nativeType] at represented
  cases represented with
  | value _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_value
      fixture atHeader outer initializer allocation parent
  | fault _ =>
    exact SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.whole_from_parent_fault
      fixture atHeader outer initializer allocation parent

include atHeader typing outer in
/-- One actual parent post supplies both its original restored body result and
its Source-derived lexical exit. No body law supplies either component. -/
theorem body_result_with_exit_of_parent
    {allocatedMap finalMap : LocationMap} {allocatedWorld finalWorld : StoreTyping}
    {allocated after : Dynamic.Heap} {allocatedStore finalStore : Store} {reference result : Value}
    {outcome : Dynamic.ExpressionOutcome} {location : Dynamic.Location} {parentSize : Nat}
    (reached : (protocol).State ⟨SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture,
      allocatedMap, allocatedWorld, allocated, allocatedStore, reference :: canonical⟩)
    (related : (protocol).Relates first reached)
    (maps : LocationMap.Extends mapping allocatedMap) (worlds : WorldExtends world allocatedWorld)
    (frame : AdministrativePreserved mapping store allocatedMap allocatedStore)
    (metadata : Dynamic.HeapMetadataExtend before allocated)
    (parentEnvironments : DataHeap.EnvRepresents
      (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
      allocatedMap allocatedWorld administrative
      (SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.parentScope fixture)
      [(fixture.graph.binder.id, location)] (reference :: canonical)
      fixture.packet.compiled.indexed.layouts.definitions)
    (parentLocals : Dynamic.EnvironmentAgrees allocated
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture).locals [(fixture.graph.binder.id, location)])
    (evidence : caller.function.evidence = [])
    (allocation : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (chosen.chosen.formation.function []))) location allocated)
    (parent : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      parentSize (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) []
      (source fixture.packet.named) [(fixture.graph.binder.id, location)] allocated
      (expressionId fixture.packet 5) outcome after)
    (post : CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt
      (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) (registry := registry) (faults := faults)
      bridge functions chosen.parent.compiler reached outcome after result finalStore finalMap finalWorld) :
    BodyResultWithExit (fixture := fixture) (inventory := inventory) (root := root) (registry := registry)
      (faults := faults) (owner := owner) (initial := initial) (packet := packet)
      (administrative := administrative) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨represented, heaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, returnedRelated, admitted⟩ := post
  have rawType : chosen.parent.compiler.original.type = caller.function.resultType := by
    rw [chosen.parent.original, fixture.graph.parentType, typing.header_result atHeader]
  have nativeType : fixture.calls.parent.type = caller.output :=
    outer.parentType.trans (by simpa only [atHeader.named] using caller.resultType)
  have runtimeAdmission := SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.post_admission_at_runtime
    fixture typing bridge returned admitted
  let restored := (CallableIndexedOwnedNestedCanonicalState.bindings (headers := headers) owner caller).restore
    (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
    (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
  refine ⟨?_, ?_⟩
  · refine ⟨?_, heaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
      metadata.trans finalMetadata, restored, ?_, ?_⟩
    · simpa only [rawType, nativeType] using represented
    · have restoredRelated : (protocol).Relates returned restored :=
        (CallableIndexedOwnedNestedCanonicalState.bindings owner caller).restore_related
          (index := ⟨initialScope fixture.packet, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := fixture.graph.binder.id) (type := fixture.calls.payload) (value := reference) returned
      exact (protocol).trans related ((protocol).trans returnedRelated restoredRelated)
    · refine ⟨runtimeAdmission.rows, ?_⟩
      intro value same
      simpa only [rawType] using runtimeAdmission.successful value same
  · have lexical := lexical_at_parent fixture typing parentEnvironments parentLocals finalMaps finalWorlds finalMetadata
    cases outcome with
    | value value =>
      obtain ⟨wholeSize, sourceBody, _parentSmall⟩ :=
        SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.body_from_parent fixture atHeader chosen.chosen typing
          (.nil before) allocation parent
      refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture, .returned value, ?_, .returned value, ?_⟩
      · simpa only [TypedScopedStatements.Executes, ↓reduceIte,
          atHeader.context, atHeader.source, atHeader.statements, evidence] using sourceBody.sound
      · simpa only [atHeader.context, atHeader.source] using lexical
    | fault reason =>
      obtain ⟨wholeSize, sourceBody, _parentSmall⟩ :=
        SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.body_from_parent fixture atHeader chosen.chosen typing
          (.nil before) allocation parent
      refine ⟨SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture, .fault reason, ?_, .fault reason, ?_⟩
      · simpa only [TypedScopedStatements.Executes, ↓reduceIte,
          atHeader.context, atHeader.source, atHeader.statements, evidence] using sourceBody.sound
      · simpa only [atHeader.context, atHeader.source] using lexical

variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
    (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation)
  (stored : RuntimeStoreHasTypes world store fixture.packet.compiled.indexed.layouts.definitions)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog fixture.packet.compiled.compatible.checked.catalog)
    mapping world administrative (initialScope fixture.packet) [] canonical fixture.packet.compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
      headers keys registry faults inventory.contracts) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before (runtimeContext fixture.packet).locals [])
  (agrees : EnvironmentsAgree captured.embedding canonical actual)
  (reference : canonical[(initialScope fixture.packet).length + 1 + fixture.packet.compiled.indexed.base.globals.length]? =
    some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type contextLocation))
  (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode fixture.packet.compiled.indexed.ancestry.layout.frame native))
  (ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller
    (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry
      (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
        headers keys registry faults inventory.contracts))).Ready ⟨initial, packet⟩ contextLocation native)
  (admitted : Admission (CallableIndexedOwnedIndirectCallerProtocol.forget_slots
    (CallableIndexedOwnedNestedCallerProtocol.carrier owner caller)) (runtimeContext fixture.packet) ⟨initial, packet⟩)

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- The genuine complete Source body constructs its initialized parent entry
once and preserves its actual whole result, effects and restored admission. -/
theorem preserves_body_with_exit (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context [] before outcome after) (within : size ≤ budget) :
    ∃ result finalStore finalMap finalWorld,
      Evaluates actual store (caller.body.rename captured.embedding) result finalStore ∧
      BodyResultWithExit (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) (administrative := administrative) outcome after result finalStore finalMap finalWorld := by
  obtain ⟨parentSize, location, allocated, allocatedSource, parentTrace, parentSmall⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds.source_parent_at_body fixture atHeader shape typing root chosen evidence trace
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, location)] fixture.graph.binder.id location := .head
  obtain ⟨result, finalStore, finalMap, finalWorld, parent, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentPreservationBounds.preserves_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      _ [] extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup reached
      parentAdmission budget parentTrace (Nat.le_trans (Nat.le_of_lt parentSmall) within)
  exact ⟨result, finalStore, finalMap, finalWorld,
    whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured) initializer allocation parent post.1,
    body_result_with_exit_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata parentEnvironments parentLocals evidence allocatedSource parentTrace post⟩

include atHeader shape typing checked outer prefixContext extension observed stored environments heaps locals agrees reference read ready admitted in
/-- Native completion constructs its Source allocation and body independently.
The authentic child budget is retained; whole determinism aligns its final post. -/
theorem reflects_body_with_exit (evidence : caller.function.evidence = []) (budget : Nat)
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (caller.body.rename captured.embedding) result finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context [] before outcome after ∧
      BodyResultWithExit (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults) (owner := owner)
        (initial := initial) (packet := packet) (administrative := administrative)
        outcome after result finalStore finalMap finalWorld := by
  have allocatedSource : Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
      (some (.closure (chosen.chosen.formation.function []))) _ _ := .append
  obtain ⟨_sourceInitializer, initializer, _determined, entry⟩ :=
    SourceCoreChosenOrdinaryAcceptedInitializedEntry.initialized_entry fixture atHeader shape typing checked inventory
      root chosen outer captured prefixContext owner initial packet observed stored environments heaps locals agrees
      reference read allocatedSource ready admitted
  obtain ⟨_allocationCapture, _captures, _captureTyped, allocation, parentEnvironments, parentHeaps, parentLocals,
    parentAgrees, parentTyped, _parentReference, _parentRead, allocationFrame, maps, worlds, allocationMetadata,
    _freshReference, actualStored, reached, related, _poolRelated, parentAdmission⟩ := entry
  obtain ⟨parentSize, parentResult, parentStore, parentWithin, parent⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyBounds.parent_within_whole_budget fixture atHeader outer initializer allocation
      budget completed within
  have lookup : Dynamic.Environment.LooksUp [(fixture.graph.binder.id, ⟨before.cells.length⟩)]
      fixture.graph.binder.id ⟨before.cells.length⟩ := .head
  obtain ⟨parentSourceSize, outcome, after, finalMap, finalWorld, parentTrace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedParentReflectionBounds.reflects_parent_at_initialized
      fixture atHeader shape typing inventory root chosen bridge (captured.extend maps worlds) prefixContext
      reached extension parentEnvironments parentHeaps parentLocals parentAgrees parentTyped actualStored lookup parentAdmission
      budget parent parentWithin
  have whole := whole_of_parent (fixture := fixture) (atHeader := atHeader) (inventory := inventory)
      (root := root) (chosen := chosen) (outer := outer) (captured := captured)
    initializer allocation parent.sound post.1
  obtain ⟨sameResult, sameStore⟩ := evaluation_deterministic whole completed.sound
  subst result
  subst finalStore
  obtain ⟨sourceSize, sourceBody, _sourceParentSmall⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction.body_trace_at_header fixture atHeader chosen.chosen typing
      evidence (.nil before) allocatedSource parentTrace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceBody,
    body_result_with_exit_of_parent fixture atHeader typing inventory root chosen outer owner initial packet reached related maps worlds
      allocationFrame allocationMetadata parentEnvironments parentLocals evidence allocatedSource parentTrace post⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts
/-! The genuine initialized body exit is retained at its original named
parameter receipt. The full lexical administrative context comes from that
same BodyState, independently of the shorter creator capture. Source and
native ports retain the original returned pool, effects and post admission. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  (runtime : SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence.RuntimeEvidence fixture caller)
  (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
  (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
  (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
  (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
  {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete
    (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) headers)
  (prefixZero : owner.key.capturePrefix = 0)
  {index : ProtectedStateTransition.Index} {argumentsPool : State headers keys index}
  {arguments : List Dynamic.Value}
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
      (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts)
    owner argumentsPool caller arguments)

local notation "functions" => CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
  (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture) headers keys registry faults inventory.contracts
local notation "model" => CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions
local notation "protocol" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "bridge" => CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)
local notation "baseBridge" => CallableIndexedOwnedIndirectCallerProtocol.of_legacy
  (CallableIndexedOwnedCallerProtocol.base (headers := headers) (keys := keys))

/-- Only the proof of the empty Source environment is transported. Every
native capture field comes from the original actual parameter BodyState. -/
def creation_capture : Captures fixture.packet.compiled.indexed receipt.body.mapping receipt.body.world
    (initialScope fixture.packet) (chosen.chosen.formation.function []).captured receipt.body.actualBody := by
  let captured := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry
    fixture functions owner receipt complete prefixZero runtime.globals
  exact {
    administrative := captured.administrative
    canonical := captured.canonical
    actualContext := captured.actualContext
    embedding := captured.embedding
    represented := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
        (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1,
        CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation.function, CallableIndexedLambdaGeneration.closure]
        using captured.represented
    agrees := captured.agrees
    respects := by
      simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using captured.respects
    typed := captured.typed }

include runtime prefixZero in
/-- The packet and the pool are those of the same original receipt. -/
theorem input_packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller
    ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
      receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ receipt.reached := by
  let original := receipt.packet prefixZero runtime.globals
  refine ⟨?_, ?_, ?_, original.carried⟩
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.globals
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.reference
  · simpa only [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original.bundle

include runtime prefixZero in
/-- The actual body evaluation, lexical exit and admission retain one returned
state. Only the genuine Header and empty parameter environment are transported. -/
private theorem result_at_receipt {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (evaluated : Evaluates receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore)
    (post : SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.BodyResultWithExit
      (fixture := fixture) (inventory := inventory) (root := root) (registry := registry) (faults := faults)
      (owner := owner) (canonical := receipt.body.canonical) (initial := receipt.reached)
      (packet := input_packet fixture runtime inventory root owner prefixZero receipt)
      (administrative := SourceCoreCompatibleCatalog.packTypes (caller.bindings.map Prod.snd) :: receipt.administrative)
      outcome after value finalStore finalMap finalWorld) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ResultAt receipt (faults := faults)
      outcome after value finalStore finalMap finalWorld := by
  obtain ⟨⟨represented, heaps, maps, worlds, frame, metadata, returned, related, admitted⟩, exited⟩ := post
  refine ⟨evaluated, represented, heaps, maps, worlds, frame, metadata, ?_, returned.val, related, ?_⟩
  · simpa only [CallableIndexedAmbient.ambient_definitions, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1]
      using exited
  · refine ⟨admitted.rows, ?_⟩
    intro sourceValue same
    simpa only [runtime.toHeaderAt.context] using admitted.successful sourceValue same

variable (extension : SourceCoreRawMetadata.Extends
  (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry)

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- One genuine outer body proof supplies the existing strong Source receipt
contract, including its actual stopping context and same returned admission. -/
theorem source_preserves_at_receipt (size : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt receipt (faults := faults) size := by
  intro outcome after trace
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  have originalTrace := trace
  rw [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at originalTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.preserves_body_with_exit fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence size originalTrace (Nat.le_refl size)
  exact ⟨value, finalStore, finalMap, finalWorld,
    result_at_receipt fixture runtime inventory root owner prefixZero receipt evaluated post⟩

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- One genuine native body child supplies an independent Source grade and the
existing strong receipt result at the same original input and final state. -/
theorem native_reflects_at_receipt (size : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt receipt (faults := faults) size := by
  intro value finalStore completed
  let captured := creation_capture fixture runtime inventory root chosen owner complete prefixZero receipt
  let packet := input_packet fixture runtime inventory root owner prefixZero receipt
  let first : (protocol).State ⟨initialScope fixture.packet, receipt.body.mapping, receipt.body.world,
    receipt.body.heap, receipt.body.store, receipt.body.canonical⟩ := ⟨receipt.reached, packet⟩
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := fixture.packet.compiled.indexed)
      (values := .initial fixture.packet.compiled.compatible.checked) (program := Program.ofChecked fixture.packet.compiled.sourceProgram)
      headers owner.key.locations 1 (initialScope fixture.packet) captured.canonical owner.key.frameLocation := by
    have original := SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captured_globals fixture functions owner receipt complete prefixZero runtime.globals
    simpa only [captured, creation_capture, SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt] using original
  have ready : (CallableIndexedOwnedNestedCanonicalState.markedProducer (headers := headers) owner caller model).Ready
      first receipt.frameLocation (.state receipt.index) := by
    apply CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner caller model receipt.stable_owner
    exact receipt.body.state.read
  have admitted : Admission bridge (runtimeContext fixture.packet) first :=
    ⟨SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_heap_typed fixture runtime.toHeaderAt functions owner receipt, receipt.rows⟩
  have environments := receipt.body.environments
  rw [SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt,
    (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] at environments
  have reference := receipt.body.reference
  have scopeLength : (initialScope fixture.packet).length = caller.bindings.length := by
    rw [← SourceCoreChosenOrdinaryAcceptedBodyStatePorts.scope_at_entry fixture runtime.toHeaderAt, List.length_map, List.length_reverse]
  rw [← scopeLength, runtime.globals] at reference
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, post⟩ :=
    SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit.reflects_body_with_exit fixture runtime.toHeaderAt shape typing checked inventory
      root chosen outer captured rfl owner receipt.reached packet extension observed
      receipt.body.heaps.runtime_hasTypes environments receipt.body.heaps
      (SourceCoreChosenOrdinaryAcceptedBodyStatePorts.source_locals fixture runtime.toHeaderAt functions owner receipt)
      receipt.body.lookups reference receipt.body.state.read ready admitted runtime.evidence size completed (Nat.le_refl size)
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_,
    result_at_receipt fixture runtime inventory root owner prefixZero receipt completed.sound post⟩
  simpa only [(SourceCoreChosenOrdinaryAcceptedBodyStatePorts.empty_entry fixture runtime.toHeaderAt functions owner receipt).2.1] using trace

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Every strict Source body child uses its own original receipt. The supplied
prefix agreement is retained by the unchanged callback interface. -/
theorem source_bodies_for (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.SourceBodiesFor
      (headers := headers) («functions» := functions) (owner := owner) (registry := registry) (faults := faults) caller budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _strict
  exact source_preserves_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete
    prefixZero actualReceipt extension size

include runtime chosen shape typing checked outer complete prefixZero extension in
/-- Every strict native child retains the original prefix and saved restoration
indices while reflecting to its own independent Source grade. -/
theorem native_bodies_for (budget : Nat) :
    CallableIndexedOwnedPreparedNamedParameterReceipts.NativeBodiesFor
      (headers := headers) («functions» := functions) (owner := owner) (registry := registry) (faults := faults) caller budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore _prefix _prefixSmall _restored size _strict
  exact native_reflects_at_receipt fixture runtime shape typing checked inventory root chosen outer owner complete
    prefixZero actualReceipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
/-! The original public bootstrap supplies the concrete singleton catalog and
its positive initialized capture. One real named hook and parameter prefix
produce the same admission-bearing body receipt, without a Source body law. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog
open CallableIndexedOwnedFunctionState RecursiveNamedCatalogInvocationBounds
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

/-- The actual singleton header order and fixed physical initialization key. -/
def headers (fixture : AcceptedFixture) (header : ActualHeader fixture) := [header]

def key (fixture : AcceptedFixture) : CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
    (Program.ofChecked fixture.packet.compiled.sourceProgram) :=
  ⟨fun header => RecursiveNamedCatalogInitialization.location fixture.packet.compiled.indexed.base.globals header.slot, 0, 0⟩

def keys (fixture : AcceptedFixture) := [key fixture]

def owner (fixture : AcceptedFixture) : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture) :=
  ⟨⟨0, by simp [keys]⟩⟩

theorem bindings_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.bindings = [] := by
  have empty : header.bindings.map Prod.fst = [] := header.parameters.symm.trans atHeader.parameters
  exact List.map_eq_nil_iff.mp empty

theorem types_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.types = [] := by
  have length := header.extended.length_eq
  rw [atHeader.parameters, List.length_nil] at length
  exact List.eq_nil_of_length_eq_zero length.symm

theorem locals_empty (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) : header.function.context.locals = [] := by
  rw [atHeader.functionContext]
  rfl

theorem catalog_complete (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {header : ActualHeader fixture} (atHeader : HeaderAt fixture header) :
    RecursiveNamedCatalogNativeContexts.Complete
      (prepared := fixture.packet.compiled.indexed.ancestry) (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) (headers fixture header) := by
  intro index signature found
  rw [CallableIndexedPreparedInventories.cached_globals, functions_singleton prepared] at found
  simp only [List.map_cons, List.map_nil] at found
  cases index with
  | zero =>
    have same : fixture.packet.named.signature = signature := Option.some.inj found
    exact ⟨header, List.mem_singleton_self header, atHeader.slot, atHeader.named ▸ same⟩
  | succ index => simp at found

theorem catalog_ledger (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (atHeader : HeaderAt fixture header) :
    Ledger (headers fixture header) fixture.packet.compiled.indexed.secondPass.closures := by
  refine ⟨?_, ?_, ?_⟩
  · change [header.slot].Nodup
    simp
  · have programEq := (SourceCoreUnifiedPreparationCertificates.prepare_fields fixture.packet.compiledAccepted).1
    have ids := (Frontend.checkProgram_success_ids fixture.packet.checked).1
    have unique := (SignatureCatalogWellFormed.ofCheckProgram fixture.packet.checked).function_ids
    simp only [Program.ofChecked, List.map_map, Function.comp_def,
      FunctionDefinition.ofChecked, BodyDefinition.ofChecked]
    rw [programEq, ids]
    exact unique
  · intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    rw [atHeader.slot, atHeader.named, atHeader.code]
    exact fixture.packet.cached.trans (congrArg some fixture.tail.emitted)

/-- The actual returned Entry and prescribed capture share the completed
bootstrap store. Frame history and records are retained constructor facts. -/
structure InitialAt (fixture : AcceptedFixture) (header : ActualHeader fixture)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) (world : StoreTyping) (store : Store) where
  catalog : Entry (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (headers fixture header) (key fixture).locations 0 0 [] [] world ⟨[]⟩ store
    (RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled)
  heaps : CompatibleAmbientHeap.HeapRepresents fixture.packet.compiled.compatible.checked registry functions
    [] world ⟨[]⟩ store
  frameLocation : catalog.authority.frameLocation = 0
  current : catalog.authority.current = .empty
  ghost : catalog.authority.ghost = .empty
  records : catalog.authority.records = []
  capture : Capture (prepared := fixture.packet.compiled.indexed.ancestry)
    (values := .initial fixture.packet.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
    (headers fixture header) (key fixture).locations 0 0 header [] world ⟨[]⟩ store
  canonical : capture.canonical = RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled
  captured : capture.captured = List.replicate header.slot Value.unit ++
    RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled
  embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot

def InitialAt.state {fixture : AcceptedFixture} {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store, RecursiveNamedCatalogPreparedInitialization.environment fixture.packet.compiled⟩ where
  rows i := by
    have same : i = (owner fixture).position := by
      apply Fin.ext
      have bound := i.isLt
      change i.val < 1 at bound
      change i.val = 0
      omega
    subst i
    exact ⟨initial.catalog.authority, initial.frameLocation⟩
  separated := by
    intro i j record member
    have same : i = (owner fixture).position := by
      apply Fin.ext
      have bound := i.isLt
      change i.val < 1 at bound
      change i.val = 0
      omega
    subst i
    change record ∈ initial.catalog.authority.records at member
    rw [initial.records] at member
    cases member

theorem InitialAt.stable {fixture : AcceptedFixture} {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows initial.state := by
  intro i
  have same : i = (owner fixture).position := by
    apply Fin.ext
    have bound := i.isLt
    change i.val < 1 at bound
    change i.val = 0
    omega
  subst i
  change ∃ metadata, Carries fixture.packet.compiled.indexed.ancestry.graph.inputs
    fixture.packet.compiled.indexed.ancestry.graph.table initial.catalog.authority.current
      initial.catalog.authority.ghost metadata
  rw [initial.current, initial.ghost]
  exact ⟨none, .empty⟩

/-- One authentic preparation types the actual initialized store. The same
completed original machine supplies its exact store equality. -/
theorem initial_at_completed (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (InitialAt fixture header functions registry world completed.store) := by
  have sameStore := (completed_store completed).2
  rw [sameStore]
  have sizes : ∀ selected, selected ∈ headers fixture header →
      selected.globals = fixture.packet.compiled.indexed.base.globals.length := by
    intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    exact bootstrap.globals
  have locals : ∀ selected, selected ∈ headers fixture header → selected.function.context.locals = [] := by
    intro selected member
    have same : selected = header := List.mem_singleton.mp member
    subst selected
    exact locals_empty fixture bootstrap.toHeaderAt
  obtain ⟨world, catalog, heaps, constructed⟩ :=
    RecursiveNamedCatalogPreparedInitializationReceipts.entry_with_constructor
      (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (program := Program.ofChecked fixture.packet.compiled.sourceProgram) fixture.packet.compiled (headers fixture header) (catalog_ledger fixture bootstrap.toHeaderAt)
      sizes locals prepared.accepted rfl functions registry
  obtain ⟨capture, captured⟩ := constructed.captures header (List.mem_singleton_self header)
  exact ⟨world, ⟨⟨catalog, heaps, constructed.frameLocation, constructed.current,
    constructed.ghost, constructed.records, capture, captured.canonical, captured.captured, captured.embedding⟩⟩⟩

private theorem readyAt_layout {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem related_frame {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

/-- The genuine original parameter prefix is retained beside its same body
input and reached pool. Both Source argument lists are actually empty. -/
def ParameterAgreement (fixture : AcceptedFixture) {header : ActualHeader fixture}
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store)
    (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      functions (owner fixture) initial.state header []) : Prop :=
  ContinuationAgreement receipt.actual
    (store.set receipt.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state receipt.index)))
    (header.parameterCode.rename receipt.embedding) receipt.body.actualBody receipt.body.store
    (header.body.rename receipt.body.embedding)

/-- One real named hook installation and one original stateful parameter
producer yield the complete actual parameter Receipt and continuation prefix. -/
theorem parameters_at_initial (fixture : AcceptedFixture) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    {functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {store : Store}
    (initial : InitialAt fixture header functions registry world store) :
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        functions (owner fixture) initial.state header [], ParameterAgreement fixture initial receipt := by
  let authority := initial.catalog.authority
  have frameZero : authority.frameLocation = 0 := initial.frameLocation
  have physical : authority.frameLocation = (owner fixture).key.frameLocation := frameZero
  obtain ⟨origin, index, metadata, selected, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history fixture.packet.compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install initial.state (owner fixture).position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have written : store.write? authority.frameLocation
      (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)) =
      some (store.set authority.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index))) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp authority.frame.read).1, rfl⟩
  let nextCapture : Capture (prepared := fixture.packet.compiled.indexed.ancestry)
      (values := .initial fixture.packet.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed)
      (headers fixture header) (key fixture).locations 0 0 header [] world ⟨[]⟩
      (store.set authority.frameLocation (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index))) :=
    { initial.capture with read := (Store.write?_preserves_other written
      (by simpa only [frameZero] using initial.capture.distinct)).trans initial.capture.read }
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) initial.capture.embedding.lift))
      (DataPatternValues.packValues ([] : List Value) :: initial.capture.canonical)
      (.unit :: encode fixture.packet.compiled.indexed.ancestry.layout.frame authority.current ::
        DataPatternValues.packValues ([] : List Value) :: initial.capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift initial.capture.layout .unit)
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      [] world header.bindings [] [] := by
    rw [bindings_empty fixture bootstrap.toHeaderAt]
    exact .nil
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues ([] : List Value))
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped initial.capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol (headers fixture header) (keys fixture))
      header.layouts fixture.packet.compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions) :=
    bootstrap.layouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer (headers fixture header) (keys fixture)
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) :=
    readyAt_layout bootstrap.layouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (owner fixture).position physical.symm history)
  let parameterInitial : State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store.set authority.frameLocation
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)), initial.capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State (headers fixture header) (keys fixture)
      ⟨[], [], world, ⟨[]⟩, store.set location
        (encode fixture.packet.compiled.indexed.ancestry.layout.frame (.state index)), initial.capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, transition, agreement⟩ := CallableIndexedOwnedInvocationBounds.parameters_with_state installedAuthority
    nextCapture.environments nextCapture.locals (by
      change nextCapture.canonical[header.globals]? = some (.cellRef fixture.packet.compiled.indexed.ancestry.layout.frame.type authority.frameLocation)
      simpa only [frameZero] using nextCapture.reference)
    nextCapture.coherent represented
    (CallableIndexedBodyFrames.install header.registered initial.heaps authority.unmapped authority.typed
      authority.frame (.stable history)).1 layout actualTyped producer parameterInitial readyAt
  obtain ⟨reached, related⟩ := transition
  have installedRelated : Relates initial.state parameterInitial :=
    related_frame initial.state physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related initial.state (owner fixture).position (.stable history))
  have heapTyped : Dynamic.HeapWellTyped header.function.context ⟨[]⟩ := by intro cell member; cases member
  have argumentsTyped : Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ [] header.types := by
    rw [types_empty fixture bootstrap.toHeaderAt]
    exact .nil
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
      functions (owner fixture) initial.state header [] := {
    origin := origin, index := index, metadata := metadata,
    administrative := initial.capture.administrative,
    actualContext := _, actual := _, embedding := _, frameLocation := authority.frameLocation,
    physical := physical, selected := selected, history := history, emitted := emitted,
    body := entry, reached := reached, related := installedRelated.trans related,
    stable := initial.stable, heapTyped := heapTyped, argumentsTyped := argumentsTyped }
  exact ⟨receipt, agreement⟩

/-- Public preparation and completion are supplied once by the retained
executable receipt; the genuine named parameter action is then constructed. -/
theorem parameter_entry (fixture : AcceptedFixture) (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel) {header : ActualHeader fixture}
    (bootstrap : BootstrapEvidence fixture header)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, ∃ initial : InitialAt fixture header functions registry world completed.store,
      ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        functions (owner fixture) initial.state header [], ParameterAgreement fixture initial receipt := by
  obtain ⟨world, ⟨initial⟩⟩ := initial_at_completed fixture prepared completed bootstrap functions registry
  obtain ⟨receipt, agreement⟩ := parameters_at_initial fixture bootstrap initial
  exact ⟨world, initial, receipt, agreement⟩

end Tests.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
/-! The genuine public bootstrap and parameter prefix produce one actual body
receipt. Both body meanings hold at that same receipt, retaining its returned
pool and Source admission as well as the original continuation agreement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)

/-- The receiving chosen model uses the one actual root and singleton public
catalog in both the constructed initial state and the body result. -/
def functions (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) :=
  CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture) registry faults inventory.contracts

variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (functions fixture root inventory registry faults) registry world store)
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (functions fixture root inventory registry faults)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [])

/-- Every port is a conclusion at the same produced receipt. The strong body
result keeps its actual returned pool and successful Source post admission. -/
structure BodyAtReceipt : Prop where
  agreement : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.ParameterAgreement fixture initial receipt
  preserves : ∀ (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context receipt.body.environment receipt.body.heap outcome after →
    size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (caller.body.rename receipt.body.embedding) value finalStore ∧
      SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.ResultAt
        (fixture := fixture) (root := root) (inventory := inventory)
        (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
        (receipt := receipt) outcome after value finalStore finalMap finalWorld
  reflects : ∀ (budget : Nat) {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore →
    size ≤ budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context receipt.body.environment receipt.body.heap outcome after ∧
      SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.ResultAt
        (fixture := fixture) (root := root) (inventory := inventory)
        (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
        (receipt := receipt) outcome after value finalStore finalMap finalWorld
  source_body_at : ∀ size,
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size
  native_body_at : ∀ size,
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size

/-- One actual public parameter construction closes both body meanings.
Complete comes from that same public recipe; the capture prefix is literally
zero. Static Source/compiler receipts and the receiving registry stay genuine. -/
theorem at_completed (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel)
    (bootstrap : BootstrapEvidence fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry) :
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
        (functions fixture root inventory registry faults) registry world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        (functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [],
      BodyAtReceipt fixture root inventory initial receipt := by
  obtain ⟨world, initial, receipt, agreement⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.parameter_entry fixture prepared completed bootstrap
      (functions fixture root inventory registry faults) registry
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt
  have prefixZero : (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).key.capturePrefix = 0 := rfl
  refine ⟨world, initial, receipt, agreement, ?_, ?_, ?_, ?_⟩
  · intro budget size outcome after trace within
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.preserves_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension budget trace within
  · intro budget size value finalStore nativeCompleted within
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.reflects_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension budget nativeCompleted within
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.source_body_at
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.native_body_at
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
end

section
-- leanmerge: from Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts
/-! One actual public bootstrap and parameter construction retain both strong
body contracts at the same receipt, including the genuine lexical exit and
returned admission. These proof ports perform no public execution action. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}

variable
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry world store)
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [])

/-- The original parameter agreement and both strong body contracts name the
same actual receipt. Source and native grades are independently quantified. -/
structure BodyAtReceiptWithExit : Prop where
  agreement : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.ParameterAgreement fixture initial receipt
  source : ∀ size,
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt receipt (faults := faults) size
  native : ∀ size,
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt receipt (faults := faults) size

/-- The public recipe constructs the original parameter receipt once. Its
body ports retain the actual exit and returned state without low erasure. -/
theorem at_completed (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel)
    (bootstrap : BootstrapEvidence fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry) :
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [],
      BodyAtReceiptWithExit fixture root inventory initial receipt := by
  obtain ⟨world, initial, receipt, agreement⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.parameter_entry fixture prepared completed bootstrap
      (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt
  have prefixZero : (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).key.capturePrefix = 0 := rfl
  refine ⟨world, initial, receipt, agreement, ?_, ?_⟩
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.source_preserves_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.native_reflects_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts
end
