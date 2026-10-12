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
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller) :
    StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements failure control facts
    runtime covers locals heap typed trace
  cases trace with
  | @returnFault childSize mode scope context environment before after id rest node expression failure contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @expressionFault childSize mode scope context environment before after id rest node expression semicolon failure
      contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped | expressionDiscard expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
  | @assignBareFault childSize mode scope context environment before after id rest node assignment rhs target failure
      contains form _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
          | wordCompound operator _ _ _ => cases operator
  | assignBareUnbound | assignBareDangling => exact ⟨heap, .refl _⟩
  | @assignBare childSize nextSize mode scope context finalContext environment before middle written after
      id rest node assignment rhs value target updated outcome contains form snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) written :=
        .assignValue contains form (.intro (snapshot.resolves _ _ _ _) child.sound.value_plain write)
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved :=  wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before written [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @letFault childSize mode scope context environment before after id rest node binder expression failure
      contains form monomorphic child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @discard childSize nextSize mode scope context finalContext environment before middle after id rest node expression
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
  | @discardValue childSize nextSize scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value wellFormed
            runtime covers locals heap expressionTyped child
          obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          exact ⟨afterTyped, headExtends.trans tailExtends⟩
  | @ifConditionFault testSize mode scope context environment before after id rest node condition thenBody elseBody failure
      contains form test =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | ifWithoutElse conditionTyped _ | ifWithElse conditionTyped _ _ =>
          exact expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
  | @ifFault testSize branchSize mode scope context innerContext environment before middle after
      id rest node condition thenBody elseBody truth failure contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have conditionTyped : ExpressionHasType scope.source context condition .bool := by
        cases formTyped <;> assumption
      have branchTyped : ∃ final facts, StatementsHaveType scope.source control context
          (if truth then thenBody else elseBody.getD []) final facts := by
        cases formTyped with
        | ifWithoutElse _ yes =>
            cases truth with
            | true => exact ⟨_, _, yes⟩
            | false => exact ⟨_, _, .nil _ _⟩
        | ifWithElse _ yes no =>
            cases truth with
            | true => exact ⟨_, _, yes⟩
            | false => exact ⟨_, _, no⟩
      obtain ⟨branchFinal, branchFacts, branchTyped⟩ := branchTyped
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, branchExtends⟩ := statementsIH branchSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped branchTyped branch
      exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @ifFallthrough testSize branchSize nextSize mode scope context innerContext finalContext environment innerEnvironment
      before middle branchHeap after id rest node condition thenBody elseBody truth outcome contains form test branch next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) branchHeap :=
        StatementsPlain.if_execute contains form test.sound.value_plain branch.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before branchHeap [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @whileFault loopSize mode scope context environment before after id rest node condition statements failure
      contains form loop =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          exact whileIH loopSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped bodyTyped loop
  | @whileFallthrough loopSize nextSize mode scope context finalContext environment before middle after
      id rest node condition statements outcome contains form loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .whileLoop contains form loop.sound.plain
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @letUninitialized nextSize mode scope context middleContext finalContext environment before bound after id rest node
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
  | @letInitialized childSize nextSize mode scope context middleContext finalContext environment before middle bound after
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

/-- Each repeated iteration is strictly smaller, and a successful scoped body
returns its actual heap to the original loop context before the next test. -/
theorem while_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller) :
    WhileAt program registry size := by
  intro scope context bodyFinal environment before after condition statements failure control facts
    runtime covers locals heap conditionTyped bodyTyped trace
  cases trace with
  | @conditionFault testSize scope context environment before after condition statements failure test =>
      exact expressionIH testSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap conditionTyped test
  | @bodyFault testSize bodySize scope context innerContext environment before middle after condition statements failure
      test body =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped bodyTyped body
      exact ⟨afterTyped, testExtends.trans bodyExtends⟩
  | @next testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after
      condition statements outcome test body next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap statements
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped body.sound.fallthrough_scoped
      obtain ⟨afterTyped, nextExtends⟩ := whileIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers ((locals.mono testExtends).mono preserved.heap_extends) preserved.heap_typed
        conditionTyped bodyTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans nextExtends)⟩

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
