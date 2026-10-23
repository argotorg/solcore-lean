import Solcore.Frontend.SourceInference.LocalGeneralizationBoundedProgress

/-! The existing event traversal bounds every recorded initialized binder by
the actual local allocator. This includes initialized for-header binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
open TypeSystem Detail
open LocalGeneralizationEvents (Ready)

def InitializedBindersAllocated (state : State) : Prop :=
  ∀ node ∈ state.nodes, ∀ binder ∈ node.initializedLetBinders,
    binder.id.binderIndex ≤ state.nextLocal

theorem InitializedBindersAllocated.empty {state : State} (empty : state.nodes = []) :
    InitializedBindersAllocated state := by
  intro node member
  rw [empty] at member
  cases member

/-- A boundary records the exact binder allocated after its initializer. -/
theorem Boundary.binderIndex {binder : TypedBinder} {initializer : ExpressionId}
    {low high : Nat} {nodes : List Node}
    (boundary : Boundary binder initializer low high nodes) :
    binder.id.binderIndex = high := by
  cases boundary with
  | statement receipt _ _ => rfl
  | header receipt _ _ => rfl

theorem OriginSince.allocated {entry : Nat} {state : State}
    {binder : TypedBinder} {initializer : ExpressionId}
    (origin : OriginSince entry state binder initializer) :
    binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨low, high, nodes, _, boundary, barrier⟩ := origin
  rw [boundary.binderIndex]
  exact barrier.allocated

theorem ItemSince.allocated {entry : Nat} {state : State} {item : ForItemForm}
    (origin : ItemSince entry state item) :
    ∀ binder ∈ item.initializedLetBinders, binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  cases item with
  | letDecl selected initializer =>
    cases initializer with
    | none => cases member
    | some initializer =>
      have same : binder = selected := List.mem_singleton.mp member
      subst binder
      exact (origin selected initializer rfl).allocated
  | expression | assignValue | assignBitNot => cases member

theorem ItemsSince.allocated {entry : Nat} {state : State} {items : List ForItemForm}
    (origin : ItemsSince entry state items) :
    ∀ binder ∈ items.flatMap ForItemForm.initializedLetBinders,
      binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  obtain ⟨item, present, bound⟩ := List.mem_flatMap.mp member
  exact (origin item present).allocated binder bound

theorem StatementSince.allocated {entry : Nat} {state : State} {node : StatementNode}
    (origin : StatementSince entry state node) :
    ∀ binder ∈ node.form.initializedLetBinders, binder.id.binderIndex ≤ state.nextLocal := by
  intro binder member
  cases form : node.form with
  | letDecl selected initializer =>
    cases initializer with
    | none => simp [form, StatementForm.initializedLetBinders] at member
    | some initializer =>
      have same : binder = selected := by
        simpa only [form, StatementForm.initializedLetBinders, List.mem_singleton] using member
      subst binder
      have actual : OriginSince entry state selected initializer := by
        simpa only [StatementSince, form] using origin
      exact actual.allocated
  | forLoop initializer condition post body =>
    have actual : ItemsSince entry state initializer ∧ ItemsSince entry state post := by
      simpa only [StatementSince, form] using origin
    simp only [form, StatementForm.initializedLetBinders, List.mem_append] at member
    exact member.elim (actual.1.allocated binder) (actual.2.allocated binder)
  | returnStmt | expression | assignValue | assignBitNot | ifThen | block
  | matchWith | whileLoop | breakStmt | continueStmt =>
    simp [form, StatementForm.initializedLetBinders] at member

/-- Old declarations retain their complete form; new declarations expose their
actual allocation boundary. Both cases use the same operational progress. -/
theorem Progress.initializedAllocated {before after : State}
    (progress : Progress before after) (ready : Ready before)
    (below : before.LocalBindersBelowNextLocal)
    (allocated : InitializedBindersAllocated before) :
    InitializedBindersAllocated after := by
  intro node member binder bound
  cases node with
  | expression expression => cases bound
  | statement statement =>
    rcases progress.events ready below statement member with old | fresh
    · obtain ⟨prior, present, _, sameForm⟩ := old
      have boundBefore : binder ∈ (Node.statement prior).initializedLetBinders := by
        change binder ∈ prior.form.initializedLetBinders
        rw [sameForm]
        exact bound
      exact Nat.le_trans (allocated _ present _ boundBefore) progress.scope.next
    · exact fresh.allocated binder bound

end Solcore.Frontend.SourceInference.LocalGeneralizationBoundaries
