import Solcore.SourceSemantics.Staging.SelectedBranchPreservation
import Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation
import Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation
import Solcore.SourceSemantics.Staging.SelectedMatchControlPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem statements_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller)
    (whileIH : ∀ smaller, smaller < size → WhileAt program registry smaller)
    (matchIH : ∀ smaller, smaller < size → MatchAt program registry smaller)
    (matchControlIH : ∀ smaller, smaller < size → MatchControlAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller)
    (loopIH : ∀ smaller, smaller < size → ForLoopAt program registry smaller) :
    StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements outcome control facts
    runtime covers locals heap typed trace
  cases trace with
  | nil =>
      cases typed
      exact ⟨heap, .refl _, (by intro _ value equal; cases equal), by
        intro result equal; cases equal; exact ⟨rfl, locals, rfl⟩⟩
  | breaking _ _ | continuing _ _ =>
      exact ⟨heap, .refl _, (by intro _ value equal; cases equal),
        by intro result equal; cases equal⟩
  | returnUnit contains form =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _, _⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnUnit resultEq =>
          exact terminal_statements ⟨heap, .refl _, by intro value equal; cases equal; exact resultEq.symm ▸ .unit⟩
            (by intro env equal; cases equal)
  | @returnValue childSize mode scope context environment before after id rest node expression value contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _, _⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
          exact terminal_statements ⟨post.heap_typed, post.heap_extends, by
            intro actual equal; cases equal; exact post.value_typed _ rfl⟩ (by intro env equal; cases equal)
  | @tail childSize scope context environment before after id node expression value contains form child =>
      cases typed with
      | singleton headTyped =>
          have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
          cases controlTyped with
          | expressionValue expressionTyped =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              refine ⟨post.heap_typed, post.heap_extends, ?_, by intro env equal; cases equal⟩
              intro complete actual equal
              cases equal
              have resultEq := complete rfl
              simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary] at resultEq
              exact resultEq ▸ post.value_typed _ rfl
  | bitNotBareFault => exact fault_statements heap (.refl _)
  | @bitNotBare nextSize mode scope context finalContext environment before written after
      id rest node assignment target updated outcome contains form snapshot write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignBitNot assignmentTyped =>
          obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_bitNot locals heap assignmentTyped snapshot write
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono writtenExtends) writtenTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
  | @assignProjected keysSize childSize nextSize mode scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated id rest node outcome
      contains form _projected keys snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_equal savedTyped first write
              have totalExtends := keyPost.heap_extends.trans writtenExtends
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono totalExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend totalExtends
          | wordCompound kind targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              obtain ⟨root, savedTyped⟩ := projected_target_typed runtime.graph.nodeOccurrencesUnique
                locals keyPost.heap_typed keyPost.heap_extends targetTyped keyTyped (keyPost.values_typed _ rfl) snapshot
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
                runtime covers (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := projected_write_compound kind savedTyped first write
              have totalExtends := keyPost.heap_extends.trans writtenExtends
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono totalExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend totalExtends
  | assignProjectedRootFault => exact fault_statements heap (.refl _)
  | @assignProjectedKeysFault keysSize mode scope context environment before after assignment operator rhs id rest node failure
      contains form _projected _ready keys =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @assignProjectedGetterFault keysSize mode scope context environment before after assignment operator rhs values id rest node reason
      contains form _projected keys _failed =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              exact fault_statements keyPost.heap_typed keyPost.heap_extends
  | @assignProjectedRhsFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target id rest node failure
      contains form _projected keys _snapshot child =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              exact fault_statements post.heap_typed (keyPost.heap_extends.trans post.heap_extends)
  | @assignProjectedWriteFault keysSize childSize mode scope context environment before targetHeap after assignment operator rhs values target right id rest node reason
      contains form _projected keys _snapshot child _failed =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
              obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
              have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap keyTyped keys
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
              exact fault_statements post.heap_typed (keyPost.heap_extends.trans post.heap_extends)
  | assignBareUnbound | assignBareDangling => exact fault_statements heap (.refl _)
  | @assignBare childSize nextSize mode scope context finalContext environment before middle written after
      id rest node assignment operator rhs value target updated outcome contains form snapshot child write next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal targetTyped rhsTyped _ =>
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write locals heap targetTyped snapshot first write
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
          | wordCompound kind targetTyped rhsTyped _ =>
              have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_compound kind locals heap targetTyped snapshot first write
              have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              have headFalls : headFacts.control.canFallthrough = true := by
                have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
                cases controlTyped
                rfl
              exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend writtenExtends
  | @returnFault childSize mode scope context environment before after id rest node expression failure contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | returnValue expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
  | @expressionFault childSize mode scope context environment before after id rest node expression semicolon failure
      contains form child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped | expressionDiscard expressionTyped =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
  | @assignBareFault childSize mode scope context environment before after id rest node assignment operator rhs target failure
      contains form _snapshot child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
          | wordCompound _ _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
  | @assignBareOperands childSize mode scope context environment before after id rest node assignment operator rhs
      target right currentCell initial currentSelected contains form _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, _completeTail, _fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | assignValue assignmentTyped =>
          cases assignmentTyped with
          | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
                runtime covers locals heap rhsTyped child
              exact fault_statements post.heap_typed post.heap_extends
  | @letFault childSize mode scope context environment before after id rest node binder expression failure
      contains form monomorphic child =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ _ =>
          have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap expressionTyped child
          exact fault_statements post.heap_typed post.heap_extends
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @ifConditionFault testSize mode scope context environment before after id rest node condition thenBody elseBody failure
      contains form test =>
      obtain ⟨middle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | ifWithoutElse conditionTyped _ | ifWithElse conditionTyped _ _ =>
          have post := expressionIH testSize (Size.child_lt_stepSize (by simp))
            runtime covers locals heap conditionTyped test
          exact fault_statements post.heap_typed post.heap_extends
  | @forInitializerFault initialSize mode scope context failedContext environment before after id rest node initial condition post body
      failure contains form initialTrace =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, _tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped _ _ _ =>
          have post := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          exact fault_statements post.heap_typed post.heap_extends
  | @discard childSize nextSize mode scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionDiscard expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap expressionTyped child
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend headExtends
  | @discardValue childSize nextSize scope context finalContext environment before middle after id rest node expression
      value outcome contains form child next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | expressionValue expressionTyped =>
          obtain ⟨_valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap expressionTyped child
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            runtime covers (locals.mono headExtends) middleTyped tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend headExtends
  | @letUninitialized nextSize mode scope context middleContext finalContext environment before bound after id rest node
      binder location outcome contains form monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
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
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact ((continue_tail headFalls completeTail fallthroughWhole next post).transportEntry runtime fields).prepend (allocationExtends)
  | @letInitialized childSize nextSize mode scope context middleContext finalContext environment before middle bound after
      id rest node binder expression value location outcome contains form child monomorphic extension allocate next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | letInitialized expressionTyped _ staticExtension =>
          have sameContext := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension staticExtension
          subst staticMiddle
          obtain ⟨valueTyped, middleTyped, headExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
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
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp))
            (runtime.transport fields) (fields.covers covers) boundEnvironment boundAtMiddle tailTyped next
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          exact ((continue_tail headFalls completeTail fallthroughWhole next post).transportEntry runtime fields).prepend (headExtends.trans allocationExtends)
      | letInitializedGeneralized polymorphic _ _ _ _ => exact (polymorphic monomorphic).elim
  | @ifReturned testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth value contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements first (by intro env equal; cases equal)
  | @ifContinuing testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @ifBreaking testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth innerEnvironment contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @ifFault testSize branchSize mode scope context innerContext environment before middle after id rest node condition thenBody elseBody truth failure contains form test branch =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      exact fault_statements first.heap_typed first.heap_extends
  | @ifFallthrough testSize branchSize nextSize mode scope context innerContext finalContext environment innerEnvironment before middle branchHeap after id rest node condition thenBody elseBody truth outcome contains form test branch next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) branchHeap :=
        StatementsPlain.if_execute contains form test.sound.value_plain branch.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      obtain ⟨first, firstFalls⟩ := if_branch expressionIH statementsIH
        (Size.child_lt_stepSize (by simp)) (Size.child_lt_stepSize (by simp)) runtime covers locals heap controlTyped test branch
      have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped next
      exact (continue_tail (firstFalls _ rfl) completeTail fallthroughWhole next post).prepend first.heap_extends
  | @blockReturned innerSize mode scope context innerContext environment before after id rest node statements value contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, first.returned (by simp)⟩ (by intro env equal; cases equal)
  | @blockContinuing innerSize mode scope context innerContext environment before after id rest node statements innerEnvironment contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @blockBreaking innerSize mode scope context innerContext environment before after id rest node statements innerEnvironment contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact terminal_statements ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩ (by intro env equal; cases equal)
  | @blockFault innerSize mode scope context innerContext environment before after id rest node statements failure contains form inner =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          exact fault_statements first.heap_typed first.heap_extends
  | @blockFallthrough innerSize nextSize mode scope context innerContext finalContext environment innerEnvironment before middle after id rest node statements outcome contains form inner next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have execution : StatementExecutes program context scope.evidence scope.source environment before id
          context (.fallthrough environment) middle := .block contains form inner.sound.fallthrough_scoped
      have sameContext := execution.final_context_of_typing runtime.graph headTyped
      subst staticMiddle
      have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases controlTyped with
      | block innerTyped =>
          have first := statementsIH innerSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap innerTyped inner
          have headFalls := ControlSummary.eraseValue_canFallthrough (first.fallthrough _ rfl).2.2
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends

  | @whileReturned loopSize mode scope context environment before after id rest node condition statements value contains form loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          exact terminal_statements first (by intro env equal; cases equal)
  | @whileFault loopSize mode scope context environment before after id rest node condition statements failure contains form loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          exact fault_statements first.heap_typed first.heap_extends
  | @whileFallthrough loopSize nextSize mode scope context finalContext environment before middle after id rest node condition statements outcome contains form loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | whileLoop conditionTyped bodyTyped =>
          have first := whileIH loopSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap conditionTyped bodyTyped loop
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends
  | @matchReturned matchSize mode scope context environment before after id rest node resolution value contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
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
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchContinuing matchSize mode scope context environment before after id rest node resolution contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
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
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchBreaking matchSize mode scope context environment before after id rest node resolution contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
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
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact terminal_statements first (by intro env equal; cases equal)
  | @matchFault matchSize mode scope context environment before after id rest node resolution failure contains form matched =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
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
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      exact fault_statements first.heap_typed first.heap_extends
  | @matchFallthrough matchSize nextSize mode scope context finalContext environment before middle after id rest node resolution outcome contains form matched next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      have same : staticMiddle = context := by cases formTyped <;> rfl
      subst staticMiddle
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
      have first := matchIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped casesTyped defaults matched
      have headFalls := matchControlIH matchSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap
        (statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form) matched rfl
      have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped next
      exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends
  | @forReturned initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after id rest node initial condition post body value contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          exact terminal_statements first (by intro env equal; cases equal)
  | @forFault initialSize loopSize mode scope context loopContext environment loopEnvironment before initialized after id rest node initial condition post body failure contains form initialTrace loop =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          exact fault_statements first.heap_typed first.heap_extends
  | @forFallthrough initialSize loopSize nextSize mode scope context loopContext finalContext environment loopEnvironment before initialized middle after id rest node initial condition post body outcome contains form initialTrace loop next =>
      obtain ⟨staticMiddle, headFacts, tailFacts, headTyped, tailTyped, completeTail, fallthroughWhole⟩ := statement_head_tail typed
      have formTyped := statement_form runtime.graph.nodeOccurrencesUnique headTyped contains form
      cases formTyped with
      | forLoop initialTyped conditionTyped bodyTyped postTyped =>
          have initialPost := itemsIH initialSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initialTyped initialTrace
          obtain ⟨same, initialLocals⟩ := initialPost.done _ rfl
          subst loopContext
          have fields := ForItemsHaveType.runtimeContextFields initialTyped
          have loopClosed := fields.targetClosed runtime.closed
          have initialAtLoop := initialPost.heap_typed.transportClosed fields.signatures runtime.closed loopClosed
            runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
          have loopPost := loopIH loopSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
            (fields.covers covers) initialLocals initialAtLoop conditionTyped bodyTyped postTyped loop
          have first : ControlPreserved context before _ control.returnType _ := ⟨
            loopPost.heap_typed.transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
            initialPost.heap_extends.trans loopPost.heap_extends,
            fun value equal => (loopPost.returned value equal).transportClosed fields.signatures.symm loopClosed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
          have headFalls : headFacts.control.canFallthrough = true := by
            have controlTyped := statement_control_form runtime.graph.nodeOccurrencesUnique headTyped contains form
            cases controlTyped
            rfl
          have post := statementsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono first.heap_extends) first.heap_typed tailTyped next
          exact (continue_tail headFalls completeTail fallthroughWhole next post).prepend first.heap_extends

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
