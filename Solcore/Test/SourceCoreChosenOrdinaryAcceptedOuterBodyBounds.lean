import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentPreservationBounds
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedParentReflectionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedChosenOrdinaryInitializedAllocationState
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedInitializerAdmission

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

/-- Finite Source inversion retains the original initializer, actual Source
allocation and parent outcome, including faults after the successful let. -/
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
    ∃ initializerSize parentSize location middle outcome,
      SourceExecutionSize.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
        initializerSize (runtimeContext fixture.packet) [] (source fixture.packet.named) environment before
        (expressionId fixture.packet 1)
        (.closure (SourceCoreChosenOrdinaryAcceptedInitializerAdmission.initializer fixture [] environment)) before ∧
      Dynamic.Heap.Allocates before fixture.graph.binder.scheme.body
        (some (.closure (SourceCoreChosenOrdinaryAcceptedInitializerAdmission.initializer fixture [] environment))) location middle ∧
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
  · obtain ⟨child, tailSize, sourceValue, location, middle, allocatedHeap, evaluated, allocated, tail,
      childSmall, tailSmall⟩ := completed
    obtain ⟨valueEq, heapEq⟩ := SourceCoreChosenOrdinaryAcceptedInitializerAdmission.values_at
      fixture shape [] environment evaluated.sound
    subst sourceValue
    subst middle
    obtain ⟨contextEq, parentSize, outcome, parent, controlEq, parentSmall⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.returning fixture.runtime.source_runtime.graph.nodeOccurrencesUnique
        fixture.graph.outerReturnFound fixture.graph.outerReturnForm tail
    exact ⟨contextEq, child, parentSize, location, allocatedHeap, outcome, evaluated, allocated,
      parent, controlEq, childSmall, Nat.lt_trans parentSmall tailSmall⟩

end Tests.SourceCoreChosenOrdinaryAcceptedOuterBodyBounds
