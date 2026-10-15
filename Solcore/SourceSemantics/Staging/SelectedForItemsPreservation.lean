import Solcore.SourceSemantics.Staging.SelectedBitNotWritePreservation
import Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem for_items_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (itemsIH : ∀ smaller, smaller < size → ForItemsAt program registry smaller) :
    ForItemsAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after items outcome control
    runtime covers locals heap typed trace
  cases trace with
  | empty =>
      cases typed
      exact ⟨heap, .refl _, by intro environment equal; cases equal; exact ⟨rfl, locals⟩⟩
  | @absent nextSize scope context middleContext finalContext environment before bound after binder rest location outcome
      mono extended allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | letUninitialized _staticMono _generalizes staticExtended =>
              have same := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extended staticExtended
              cases same
              have allocationExtends := HeapTypesExtend.of_allocation allocated
              have boundTyped := heap.allocate (.none _) allocated
              have boundLocals : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
                cases extended
                exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono allocationExtends)
              have fields := RuntimeContextFields.ofBinderExtends extended
              have closed := fields.targetClosed runtime.closed
              have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed closed
                runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
                (fields.covers covers) boundLocals boundAtMiddle tailTyped next
              exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
                (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
                allocationExtends.trans post.heap_extends, post.done⟩
  | @initialized childSize nextSize scope context middleContext finalContext environment before middle bound after
      binder initializer rest value location outcome mono extended child allocated next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | letInitialized initializerTyped _mono _generalizes staticExtended =>
              have same := Solcore.SourceSemantics.Dynamic.BinderExtends.functional extended staticExtended
              cases same
              have childPost := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
              have allocationExtends := HeapTypesExtend.of_allocation allocated
              have boundTyped := childPost.heap_typed.allocate (.some (childPost.value_typed _ rfl)) allocated
              have boundLocals : EnvironmentAgrees bound middleContext.locals ((binder.id, location) :: environment) := by
                cases extended
                exact .cons allocated.reads_new rfl (.ordinary mono rfl) (locals.mono (childPost.heap_extends.trans allocationExtends))
              have fields := RuntimeContextFields.ofBinderExtends extended
              have closed := fields.targetClosed runtime.closed
              have boundAtMiddle := boundTyped.transportClosed fields.signatures runtime.closed closed
                runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) (runtime.transport fields)
                (fields.covers covers) boundLocals boundAtMiddle tailTyped next
              exact ⟨post.heap_typed.transportClosed fields.signatures.symm closed runtime.closed
                (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
                childPost.heap_extends.trans (allocationExtends.trans post.heap_extends), post.done⟩
          | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @initializerFault childSize scope context environment before after binder initializer rest failure mono child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | letInitialized initializerTyped _ _ _ =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap initializerTyped child
              exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
          | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
  | @expression childSize nextSize scope context finalContext environment before middle after expression rest value outcome child next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | expression expressionTyped =>
              have first := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono first.heap_extends) first.heap_typed tailTyped next
              exact ⟨post.heap_typed, first.heap_extends.trans post.heap_extends, post.done⟩
  | @expressionFailure childSize scope context environment before after expression rest failure child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | expression expressionTyped =>
              have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap expressionTyped child
              exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignment keysSize childSize nextSize scope context finalContext environment before targetHeap middle written after assignment operator rhs values target value updated rest outcome
      _projected keys snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
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
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono totalExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, totalExtends.trans post.heap_extends, post.done⟩
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
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono totalExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, totalExtends.trans post.heap_extends, post.done⟩
  | projectedAssignmentRootFault => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩
  | @projectedAssignmentKeysFault keysSize scope context environment before after assignment operator rhs rest failure
      _projected _ready keys =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentGetterFault keysSize scope context environment before after assignment operator rhs values rest reason
      _projected keys _failed =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  exact ⟨keyPost.heap_typed, keyPost.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentRhsFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target rest failure
      _projected keys _snapshot child =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  exact ⟨post.heap_typed, keyPost.heap_extends.trans post.heap_extends, by intro environment equal; cases equal⟩
  | @projectedAssignmentWriteFault keysSize childSize scope context environment before targetHeap after assignment operator rhs values target right rest reason
      _projected keys _snapshot child _failed =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ | wordCompound _ targetTyped rhsTyped _ =>
                  obtain ⟨keyTypes, keyTyped⟩ := projected_place_keys_typed targetTyped
                  have keyPost := expressionsIH keysSize (Size.child_lt_stepSize (by simp))
                    runtime covers locals heap keyTyped keys
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono keyPost.heap_extends) keyPost.heap_typed rhsTyped child
                  exact ⟨post.heap_typed, keyPost.heap_extends.trans post.heap_extends, by intro environment equal; cases equal⟩
  | @assignment childSize nextSize scope context finalContext environment before middle written after
      assignment operator rhs value target updated rest outcome snapshot child write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal targetTyped rhsTyped _ =>
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := bare_write locals heap targetTyped snapshot first write
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono writtenExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
              | wordCompound kind targetTyped rhsTyped _ =>
                  have first := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp))) runtime covers locals heap rhsTyped child
                  obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_compound kind locals heap targetTyped snapshot first write
                  have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                    (locals.mono writtenExtends) writtenTyped tailTyped next
                  exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
  | @assignmentFailure childSize scope context environment before after assignment operator rhs target rest failure snapshot child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal _targetTyped rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
              | wordCompound _ _ rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | @assignmentOperands childSize scope context environment before after assignment operator rhs target right
      currentCell initial currentSelected rest _snapshot child _currentRead _rootType _initialValue _pathRead _invalid =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal _ rhsTyped _ | wordCompound _ _ rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
  | bitNotFault => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩
  | @bitNot nextSize scope context finalContext environment before written after assignment target updated rest outcome
      snapshot write next =>
      cases typed with
      | cons headTyped tailTyped =>
          cases headTyped with
          | assignBitNot assignmentTyped =>
              obtain ⟨writtenTyped, writtenExtends⟩ := bare_write_bitNot locals heap assignmentTyped snapshot write
              have post := itemsIH nextSize (Size.child_lt_stepSize (by simp)) runtime covers
                (locals.mono writtenExtends) writtenTyped tailTyped next
              exact ⟨post.heap_typed, writtenExtends.trans post.heap_extends, post.done⟩
  | unbound | dangling => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
