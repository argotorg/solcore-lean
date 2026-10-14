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
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller)
    (matchIH : ∀ smaller, smaller < size → MatchAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
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
  | @assignBareFault childSize mode scope context environment before after id rest node assignment operator rhs target failure
      contains form _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
          | wordCompound _ _ rhsTyped _ =>
              exact expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
  | @assignBareOperands childSize mode scope context environment before after id rest node assignment operator rhs
      target right currentCell initial currentSelected contains form _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
              have post := expression_value wellFormed runtime covers locals heap rhsTyped child
              exact ⟨post.heap_typed, post.heap_extends⟩
  | assignBareUnbound | assignBareDangling => exact ⟨heap, .refl _⟩
  | @assignBare childSize nextSize mode scope context finalContext environment before middle written after
      id rest node assignment operator rhs value target updated outcome contains form snapshot child write next =>
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
  | @blockFault innerSize mode scope context innerContext environment before after
      id rest node statements failure contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | block innerTyped =>
          exact statementsIH innerSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap innerTyped inner
  | @blockFallthrough innerSize nextSize mode scope context innerContext finalContext environment innerEnvironment
      before middle after id rest node statements outcome contains form inner next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .block contains form inner.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩
  | @matchFault matchSize mode scope context environment before after id rest node resolution failure
      contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have common : ∃ type caseFacts,
          ExpressionHasType scope.source context resolution.scrutinee type ∧
          MatchCasesHaveType scope.source control context type resolution.cases caseFacts ∧
          (∀ statements, resolution.defaultBody = some statements →
            ∃ final facts, StatementsHaveType scope.source control context statements final facts) := by
        cases formTyped with
        | matchWithoutDefault absent scrutineeTyped casesTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by simp_all⟩
        | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
          exact ⟨_, _, scrutineeTyped, casesTyped, fun statements found => by
            cases Option.some.inj (present.symm.trans found)
            exact ⟨_, _, defaultTyped⟩⟩
      obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
      exact matchIH matchSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped casesTyped defaults matched rfl
  | @matchFallthrough matchSize nextSize mode scope context finalContext environment before middle after
      id rest node resolution outcome contains form matched next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := matched.sound.plain _ _ contains form
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
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

  | @forInitializerFault initialSize mode scope context failedContext environment before after id rest node initial condition post body
      failure contains form initialTrace =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped _ _ _ =>
          exact itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
  | @forFault initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after
      id rest node initial condition post body failure contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          obtain ⟨same, initialHeap, initialExtends, initialLocals⟩ :=
            ForItemsExecute.preserved wellFormed runtime covers locals heap initialTyped initialTrace.sound.plain
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialHeap.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          obtain ⟨afterTyped, loopExtends⟩ := loopIH loopSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) initialLocals initialAtLoop
            conditionTyped bodyTyped postTyped loop
          exact ⟨afterTyped.transportClosed fields.signatures.symm loopClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialExtends.trans loopExtends⟩
  | @forFallthrough initialSize loopSize nextSize mode scope context loopContext finalContext environment loopEnvironment
      before initialized middle after id rest node initial condition post body outcome contains form initialTrace loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .forLoop contains form initialTrace.sound.plain loop.sound.plain
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment before middle [id]
        (.fallthrough environment) control context context _ runtime covers locals heap
        (.singleton headTyped) (.cons execution .nil)
      obtain ⟨afterTyped, tailExtends⟩ := statementsIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono preserved.heap_extends) preserved.heap_typed tailTyped next
      exact ⟨afterTyped, preserved.heap_extends.trans tailExtends⟩

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
  | @continueNext testSize bodySize nextSize scope context innerContext environment innerEnvironment before middle bodyHeap after
      condition statements outcome test body next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap statements
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped body.sound.continuing_scoped
      obtain ⟨afterTyped, nextExtends⟩ := whileIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers ((locals.mono testExtends).mono preserved.heap_extends) preserved.heap_typed
        conditionTyped bodyTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans nextExtends)⟩

/-- Only the selected arm runs; its real binder frame is restored after a fault. -/
theorem match_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchAt program registry size := by
  intro scope context environment before after resolution outcome failure control type caseFacts
    runtime covers locals heap scrutineeTyped casesTyped defaultTyped trace failed
  cases trace with
  | @scrutineeFault childSize scope context environment before after resolution actualFailure scrutinee =>
      cases BodyOutcome.fault.inj failed
      exact expressionIH childSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped scrutinee
  | @patternFault childSize scope context environment before middle hidden resolution node value location
      contains scrutinee allocated invalid =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated)⟩
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      cases outcome with
      | fallthrough => cases failed
      | returned | breaking | continuing => cases failed
      | fault actualFailure =>
        cases BodyOutcome.fault.inj failed
        obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
          runtime covers locals heap scrutineeTyped scrutinee
        obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
        have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
        subst typedNode
        have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
        have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
        obtain ⟨staticBinders, staticArmContext, staticFinal, armFacts,
          bindingsTyped, bindersEq, staticExtended, armTyped, monomorphic⟩ :=
          selected.armPreserves casesTyped (valueTyped.mono hiddenExtends)
        have exactExtended : BindersExtend scope.source.owner context (bindings.map Prod.fst) staticArmContext :=
          bindersEq.symm ▸ staticExtended
        have sameContext := Solcore.SourceSemantics.Dynamic.BindersExtend.functional extended exactExtended
        subst staticArmContext
        have valuesTyped : ValuesHaveTypes context hidden (bindings.map Prod.snd)
            ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
          simpa only [List.map_map, Function.comp_def] using bindingsTyped.unzip
        have boundTyped := allocated.preservesHeapTyping hiddenTyped valuesTyped
        have boundExtends := allocated.extendsHeapTypes
        have armLocals := allocated.preservesEnvironmentAgreement exactExtended
          (fun binder member => monomorphic binder (bindersEq ▸ member))
          (locals.mono (firstExtends.trans hiddenExtends))
        have fields := Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields extended
        have armClosed := fields.targetClosed runtime.closed
        have boundAtArm := boundTyped.transportClosed fields.signatures runtime.closed armClosed
          runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
        obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
          (runtime.transport fields) (fields.covers covers) armLocals boundAtArm armTyped body
        exact ⟨afterTyped.transportClosed fields.signatures.symm armClosed runtime.closed
          (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
          firstExtends.trans (hiddenExtends.trans (boundExtends.trans bodyExtends))⟩
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      cases outcome with
      | fallthrough => cases failed
      | returned | breaking | continuing => cases failed
      | fault actualFailure =>
        cases BodyOutcome.fault.inj failed
        obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value wellFormed
          runtime covers locals heap scrutineeTyped scrutinee
        obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
        have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
        subst typedNode
        have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
        have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
        obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped statements selected.defaultBody_eq
        obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize (Size.child_lt_stepSize (by simp))
          runtime covers (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped bodyTyped body
        exact ⟨afterTyped, firstExtends.trans (hiddenExtends.trans bodyExtends)⟩
  | noBranch => cases failed

private theorem for_items_tail (wellFormed : ProgramWellFormed program)
    {size : Nat} (itemsIH : ForItemsAt program registry size)
    {scope : Scope} {control : ControlContext} {context staticMiddle runtimeMiddle staticFinal runtimeFinal : Context}
    {environment middleEnvironment : Dynamic.Environment} {before middle after : Heap}
    {item : ForItemForm} {items : List ForItemForm} {failure : Failure}
    (runtime : SourceRuntimeValid program context scope.source) (covers : scope.evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment) (heap : HeapWellTyped context before)
    (headTyped : ForItemHasType scope.source control context item staticMiddle)
    (tailTyped : ForItemsHaveType scope.source control staticMiddle items staticFinal)
    (head : ForItemExecutes program context scope.evidence scope.source environment before item
      runtimeMiddle middleEnvironment middle)
    (next : Size.ForItems program registry size scope runtimeMiddle middleEnvironment middle items runtimeFinal (.fault failure) after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨same, middleTyped, headExtends, middleLocals⟩ :=
    ForItemsExecute.preserved wellFormed runtime covers locals heap (.cons headTyped (.nil _ _))
      (.cons head .nil)
  subst runtimeMiddle
  have fields := ForItemHasType.runtimeContextFields headTyped
  have middleClosed := fields.targetClosed runtime.closed
  have heapAtMiddle := middleTyped.transportClosed fields.signatures runtime.closed middleClosed
    runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
  obtain ⟨afterTyped, tailExtends⟩ := itemsIH (runtime.transport fields) (fields.covers covers)
    middleLocals heapAtMiddle tailTyped next
  exact ⟨afterTyped.transportClosed fields.signatures.symm middleClosed runtime.closed
    (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
    headExtends.trans tailExtends⟩

/-- Successful header effects are erased and preserved independently before
using the strict faulting tail; a failed RHS never invents a write. -/
theorem for_items_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller) :
    ForItemsAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after items failure control
    runtime covers locals heap typed trace
  cases trace with
  | @absent nextSize scope context middleContext finalContext environment before bound after binder rest location outcome
      mono extended allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped (.letUninitialized mono extended allocated) next
  | @initialized childSize nextSize scope context middleContext finalContext environment before middle bound after
      binder initializer rest value location outcome mono extended child allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.letInitialized child.sound.value_plain mono extended allocated) next
  | @initializerFault childSize scope context environment before after binder initializer rest failure mono child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | letInitialized initializerTyped _ _ _ =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
        | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @expression childSize nextSize scope context finalContext environment before middle after expression rest value outcome child next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped (.expression child.sound.value_plain) next
  | @expressionFailure childSize scope context environment before after expression rest failure child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | expression expressionTyped =>
          exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
  | @assignment childSize nextSize scope context finalContext environment before middle written after
      assignment operator rhs value target updated rest outcome snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
        exact for_items_tail wellFormed (itemsIH nextSize (Size.child_lt_stepSize (by simp)))
          runtime covers locals heap headTyped tailTyped
          (.assignValue (.intro (snapshot.resolves _ _ _ _) child.sound.value_plain write)) next
  | @assignmentFailure childSize scope context environment before after assignment operator rhs target rest failure snapshot child =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
            exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
          | wordCompound _ _ rhsTyped _ =>
            exact expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
  | @assignmentOperands childSize scope context environment before after assignment operator rhs target right
      currentCell initial currentSelected rest _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      cases typed with
      | cons headTyped _ =>
        cases headTyped with
        | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
            have post := expression_value wellFormed runtime covers locals heap rhsTyped child
            exact ⟨post.heap_typed, post.heap_extends⟩
  | unbound | dangling => exact ⟨heap, .refl _⟩

/-- Finite for faults keep every condition, body, and post-header prefix. -/
theorem for_loop_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    ForLoopAt program registry size := by
  intro scope context bodyFinal postFinal environment before after condition post body failure control facts
    runtime covers locals heap conditionTyped bodyTyped postTyped trace
  cases trace with
  | @testFault testSize scope context environment before after condition post body failure test =>
      exact expressionIH testSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped test
  | @bodyFailure testSize branchSize scope context innerContext environment before middle after condition post body failure
      test branch =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      obtain ⟨afterTyped, branchExtends⟩ := statementsIH branchSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono testExtends) middleTyped bodyTyped branch
      exact ⟨afterTyped, testExtends.trans branchExtends⟩
  | @postFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.fallthrough_scoped
      obtain ⟨afterTyped, postExtends⟩ := itemsIH postTraceSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans postExtends)⟩
  | @continuePostFailure testSize branchSize postTraceSize scope context innerContext postContext environment innerEnvironment
      before middle bodyHeap after condition post body failure test branch postTrace =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.continuing_scoped
      obtain ⟨afterTyped, postExtends⟩ := itemsIH postTraceSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans postExtends)⟩
  | @iterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.fallthrough innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.fallthrough_scoped
      obtain ⟨_postContext, postHeapTyped, postExtends, _postLocals⟩ :=
        ForItemsExecute.preserved wellFormed runtime covers
          (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace.sound.plain
      obtain ⟨afterTyped, nextExtends⟩ := loopIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans (preserved.heap_extends.trans postExtends)))
        postHeapTyped conditionTyped bodyTyped postTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans (postExtends.trans nextExtends))⟩
  | @continueIterate testSize branchSize postTraceSize nextSize scope context innerContext postContext environment innerEnvironment postEnvironment
      before middle bodyHeap postHeap after condition post body outcome test branch postTrace next =>
      obtain ⟨_truthTyped, middleTyped, testExtends⟩ := expression_value wellFormed
        runtime covers locals heap conditionTyped test
      have preserved := wellFormed.wholeLanguagePreservation.statements
        context scope.evidence scope.source environment middle bodyHeap body
        (.continuing innerEnvironment) control.enterLoop bodyFinal innerContext _ runtime covers
        (locals.mono testExtends) middleTyped bodyTyped branch.sound.continuing_scoped
      obtain ⟨_postContext, postHeapTyped, postExtends, _postLocals⟩ :=
        ForItemsExecute.preserved wellFormed runtime covers
          (locals.mono (testExtends.trans preserved.heap_extends)) preserved.heap_typed postTyped postTrace.sound.plain
      obtain ⟨afterTyped, nextExtends⟩ := loopIH nextSize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (testExtends.trans (preserved.heap_extends.trans postExtends)))
        postHeapTyped conditionTyped bodyTyped postTyped next
      exact ⟨afterTyped, testExtends.trans (preserved.heap_extends.trans (postExtends.trans nextExtends))⟩

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
