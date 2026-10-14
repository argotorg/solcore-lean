import Solcore.SourceSemantics.Staging.SelectedBareWritePreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem for_items_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
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
  | @assignment childSize nextSize scope context finalContext environment before middle written after
      assignment rhs value target updated rest outcome snapshot child write next =>
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
              | wordCompound operator _ _ _ => cases operator
  | @assignmentFailure childSize scope context environment before after assignment rhs target rest failure snapshot child =>
      cases typed with
      | cons headTyped _ =>
          cases headTyped with
          | assignValue assignmentTyped =>
              cases assignmentTyped with
              | equal _targetTyped rhsTyped _ =>
                  have post := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap rhsTyped child
                  exact ⟨post.heap_typed, post.heap_extends, by intro environment equal; cases equal⟩
              | wordCompound operator _ _ _ => cases operator
  | unbound | dangling => exact ⟨heap, .refl _, by intro environment equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
