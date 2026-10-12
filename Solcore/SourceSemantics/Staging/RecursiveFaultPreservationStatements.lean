import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationSupport

/-! Faulting statement sequences preserve the heap of every executed prefix.
Typed successful initializers and real allocations precede the strict faulting
child. Lexical context transport returns heap typing to the original caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

private theorem statement_head_tail
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts,
      StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem statement_form
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {id : StatementId} {node : StatementNode} {shape : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (contains : ContainsStatement source id node) (form : node.form = shape) :
    Solcore.SourceSemantics.Dynamic.StatementHasType.FormTyping source control context shape final := by
  obtain ⟨actual, found, formTyped⟩ := Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique found).symm.trans
    (lookupStatement?_complete unique contains))
  cases same
  exact form ▸ formTyped

/-- A faulting sequence uses its actual source occurrence, initializer effects
and binder allocation, and the strictly smaller faulting child exactly once. -/
theorem statements_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    StatementsAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after statements failure control facts
    runtime covers locals heap typed trace
  cases trace with
  | @returnFault childSize scope context environment before after id rest node expression failure contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @expressionFault childSize scope context environment before after id rest node expression semicolon failure
      contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped | expressionDiscard expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @letFault childSize scope context environment before after id rest node binder expression failure
      contains form monomorphic child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @discard childSize nextSize scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionDiscard expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap expressionTyped child
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          exact ⟨afterTyped, headExtends.trans tailExtends⟩
  | @letUninitialized nextSize scope context middleContext finalContext environment before bound after id rest node
      binder location outcome contains form monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letUninitialized _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          have allocationExtends := HeapTypesExtend.of_allocation allocate
          have boundTyped := heap.allocate (.none _) allocate
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocate.reads_new rfl (.ordinary monomorphic rfl) (locals.mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            allocationExtends.trans tailExtends⟩
  | @letInitialized childSize nextSize scope context middleContext finalContext environment before middle bound after
      id rest node binder expression value location outcome contains form child monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          obtain ⟨valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap expressionTyped child
          have allocationExtends := HeapTypesExtend.of_allocation allocate
          have boundTyped := middleTyped.allocate (.some valueTyped) allocate
          have boundEnvironment : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
            cases extension
            exact .cons allocate.reads_new rfl (.ordinary monomorphic rfl)
              ((locals.mono headExtends).mono allocationExtends)
          have fields := RuntimeContextFields.ofBinderExtends extension
          have middleClosed := fields.targetClosed runtime.closed
          have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed middleClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            headExtends.trans (allocationExtends.trans tailExtends)⟩
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
