import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationApplies
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationStatements

/-! Faulting recursive staged executions preserve deep Source heap typing.
The numeric induction follows actual faulting children; successful prefixes use
their independent whole-language preservation and retain all executed effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

private theorem empty_path_type {context : Context} {source target : Ty}
    (path : CoercionPathValid context source target []) : source = target := by
  cases path
  rfl

private theorem expressions_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller) :
    ExpressionsAt program registry size := by
  intro scope context environment before after ids failure types runtime covers locals heap typed trace
  cases trace with
  | @headFault headSize scope context environment before after id ids failure head =>
      cases typed with
      | cons headTyped _ =>
          exact expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
  | @tailFault headSize tailSize scope context environment before middle after id ids value failure head tail =>
      cases typed with
      | cons headTyped tailTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap headTyped head
          obtain ⟨afterTyped, tailExtends⟩ := expressionsIH tailSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped tail
          exact ⟨afterTyped, headExtends.trans tailExtends⟩

private theorem expression_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller) :
    ExpressionAt program registry size := by
  intro scope context environment before after id failure type runtime covers locals heap typed trace
  cases trace with
  | atomicFault _ atomic _ faultRule =>
      have same := atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _⟩
  | @group childSize scope context environment before after id inner outcome occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | group innerTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped child
  | @pairLeftFault childSize scope context environment before after id left right failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap firstTyped child
  | @pairRightFault firstSize secondSize scope context environment before middle after id left right value failure
      occurrence first second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          cases elementsTyped with
          | cons firstTyped restTyped =>
              cases restTyped with
              | cons secondTyped _ =>
                  obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
                    runtime covers locals heap firstTyped first
                  obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
                    runtime covers (locals.mono firstExtends) middleTyped secondTyped second
                  exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @tupleFault childrenSize scope context environment before after id elements failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | tuple elementsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap elementsTyped children
  | @constructorFault childrenSize scope context environment before after id instantiation arguments failure occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | constructor _valid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @unaryOperandFault childSize scope context environment before after id operator operand failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap operandTyped child
  | @unaryInvalid childSize scope context environment before after id operator operand input occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | unary operandTyped _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap operandTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @binaryLeftFault firstSize scope context environment before after id left operator right failure occurrence first =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          exact expressionIH firstSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap leftTyped first
  | @binaryLeftInvalid firstSize scope context environment before after id left operator right input occurrence first _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          exact ⟨afterTyped, heapExtends⟩
  | @binaryRightFault firstSize secondSize scope context environment before middle after id left operator right input failure
      occurrence first _continues second =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          obtain ⟨afterTyped, secondExtends⟩ := expressionIH secondSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @binaryInvalid firstSize secondSize scope context environment before middle after id left operator right a b
      occurrence first _continues second _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | binary leftTyped rightTyped _ =>
          obtain ⟨_firstTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
            runtime covers locals heap leftTyped first
          obtain ⟨_secondTyped, afterTyped, secondExtends⟩ := expression_value wellFormed
            runtime covers (locals.mono firstExtends) middleTyped rightTyped second
          exact ⟨afterTyped, firstExtends.trans secondExtends⟩
  | @conditional testSize branchSize scope context environment before middle after id condition yes no truth outcome
      occurrence test branch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped yesTyped noTyped =>
          obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
            runtime covers locals heap conditionTyped test
          have branchTyped : ExpressionHasType scope.source context (if truth then yes else no) _raw := by
            split <;> assumption
          obtain ⟨afterTyped, branchExtends⟩ := expressionIH branchSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono testExtends) middleTyped branchTyped branch
          exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @conditionalFault testSize scope context environment before after id condition yes no failure occurrence test =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | conditional conditionTyped _ _ =>
          exact expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
  | @builtinArgumentsFault childrenSize scope context environment before after id callee arguments function failure
      occurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @builtinApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments function values outcome occurrence children invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | builtinCall _calleeValid argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers locals heap argumentsTyped children
          have calleeTyped : ValueHasType context argumentsHeap (.builtin ⟨function⟩)
              (.function (TypeSystem.Ty.productMany function.parameterTypes) function.returnType) := by
            simpa [BuiltinFunctionId.type] using
              (ValueHasType.builtin (context := context) (heap := argumentsHeap) ⟨function⟩)
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have argumentTyped := packing.hasType valuesTyped
          obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
            runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
          exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @directArgumentsFault childrenSize scope context environment before after id callee arguments instantiation name failure
      occurrence _calleeOccurrence children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | directCall _calleeTyped _application argumentsTyped =>
          exact expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap argumentsTyped children
  | @directApplied childrenSize invocationSize scope context environment before argumentsHeap after
      id callee arguments instantiation name values evidence outcome occurrence _calleeOccurrence valid children callEvidence invocation =>
      obtain ⟨raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) raw) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType valuesTyped
                  obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime argumentsHeapTyped calleeTyped packing argumentTyped invocation
                  exact ⟨afterTyped, argumentExtends.trans invocationExtends⟩
  | @calleeFault childSize scope context environment before after id callee arguments metadata failure occurrence child =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap calleeTyped child
  | @notCallable childSize scope context environment before after id callee arguments metadata value occurrence child _invalid =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @rejected childSize scope context environment before after id callee arguments metadata value reason occurrence child _guard =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped _ _ =>
          obtain ⟨_valueTyped, afterTyped, heapExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          exact ⟨afterTyped, heapExtends⟩
  | @argumentsFault childSize childrenSize scope context environment before middle after id callee arguments metadata value failure
      occurrence child _guard children =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨afterTyped, argumentExtends⟩ := expressionsIH childrenSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @sourceArity childSize childrenSize scope context environment before middle after id callee arguments metadata value values
      occurrence child _guard children _mismatch =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped _ =>
          obtain ⟨_valueTyped, middleTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨_valuesTyped, afterTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers (locals.mono calleeExtends) middleTyped argumentsTyped children
          exact ⟨afterTyped, calleeExtends.trans argumentExtends⟩
  | @applied childSize childrenSize invocationSize scope context environment before calleeHeap argumentsHeap after
      id callee arguments metadata value values outcome occurrence uncoerced child _guard children _arity invocation =>
      obtain ⟨_raw, _plan, formTyped⟩ := expression_form runtime.graph.nodeOccurrencesUnique typed occurrence
      cases formTyped with
      | indirectCall calleeTyped argumentsTyped application =>
          obtain ⟨valueTyped, calleeHeapTyped, calleeExtends⟩ := expression_value wellFormed
            runtime covers locals heap calleeTyped child
          obtain ⟨valuesTyped, argumentsHeapTyped, argumentExtends⟩ := expressions_values wellFormed
            runtime covers (locals.mono calleeExtends) calleeHeapTyped argumentsTyped children
          obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
          have packedTyped := packing.hasType valuesTyped
          cases application with
          | intro _count beforeEq _afterEq path =>
              rw [uncoerced] at path
              rw [← beforeEq] at packedTyped
              have argumentTyped := empty_path_type path ▸ packedTyped
              obtain ⟨afterTyped, invocationExtends⟩ := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                runtime argumentsHeapTyped (valueTyped.mono argumentExtends) packing argumentTyped invocation
              exact ⟨afterTyped, calleeExtends.trans (argumentExtends.trans invocationExtends)⟩

private theorem all (wellFormed : ProgramWellFormed program) (size : Nat) :
    ExpressionAt program registry size ∧ ExpressionsAt program registry size ∧
    AppliesAt program registry size ∧ StatementsAt program registry size ∧ WhileAt program registry size ∧ MatchAt program registry size ∧
    ForItemsAt program registry size ∧ ForLoopAt program registry size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      exact ⟨expression_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.1) (fun smaller below => (ih smaller below).2.2.1),
        expressions_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.1),
        applies_step wellFormed size (fun smaller below => (ih smaller below).2.2.2.1),
        statements_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.2.2),
        while_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.1),
        match_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.2.2.1),
        for_items_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.2.1),
        for_loop_step wellFormed size (fun smaller below => (ih smaller below).1)
          (fun smaller below => (ih smaller below).2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.2.1)
          (fun smaller below => (ih smaller below).2.2.2.2.2.2.2)⟩

/-- Any supported staged expression fault retains a deeply typed heap and all
heap type identities from its initial state. -/
theorem expression (wellFormed : ProgramWellFormed program) {size : Nat} :
    ExpressionAt program registry size := (all wellFormed size).1

/-- Ordered expression faults retain every successful prefix's effects. -/
theorem expressions (wellFormed : ProgramWellFormed program) {size : Nat} :
    ExpressionsAt program registry size := (all wellFormed size).2.1

/-- Callable faults preserve the original caller's heap typing, including
faults raised by a recursively selected global or closure body. -/
theorem applies (wellFormed : ProgramWellFormed program) {size : Nat} :
    AppliesAt program registry size := (all wellFormed size).2.2.1

/-- Faulting bodies preserve the original entry context and every executed
initializer and allocation prefix. -/
theorem statements (wellFormed : ProgramWellFormed program) {size : Nat} :
    StatementsAt program registry size := (all wellFormed size).2.2.2.1

/-- Header faults preserve the initial heap typing across every visited item. -/
theorem for_items (wellFormed : ProgramWellFormed program) {size : Nat} :
    ForItemsAt program registry size := (all wellFormed size).2.2.2.2.2.2.1

/-- Finite for faults retain all real iteration and post-header effects. -/
theorem for_loop (wellFormed : ProgramWellFormed program) {size : Nat} :
    ForLoopAt program registry size := (all wellFormed size).2.2.2.2.2.2.2

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
