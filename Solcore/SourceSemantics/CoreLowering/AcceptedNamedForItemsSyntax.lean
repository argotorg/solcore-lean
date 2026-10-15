import Solcore.SourceSemantics.CoreLowering.AcceptedNamedForItemsFlow
import Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts

/-! Genuine header actions and original typing recover each finite item receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference

theorem Items.scan {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {result : Ty} {reasonAt : ExpressionId → Word}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}
    {fuel scope items code}
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code)
    (closed : tree.closed = true) (unique : NodeOccurrencesUnique source)
    {approved : ExpressionId → Prop}
    (children : ∀ child ∈ tree.children, approved child.expression)
    (bindings : ∀ binding ∈ tree.bindings, RecursiveNamedStatementSyntaxFacts.BinderReceipt source binding.binder)
    {control : ControlContext} {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final) :
    ScopedSourceForItemsAdmission.Scan source approved items := by
  induction tree generalizing context final with
  | nil => exact .nil
  | absent projected remaining allocated ih =>
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Items.bindings])
      cases typed with
      | cons head tail =>
        exact .absent binder.1 binder.2.1 binder.2.2
          (ih closed (fun child member => children child (by simpa [Items.children] using member))
            (fun binding member => bindings binding (by simp [Items.bindings, member])) tail)
  | initialized projected child generated childType remaining allocated ih =>
      have binder := bindings ⟨_, _, _, projected⟩ (by simp [Items.bindings])
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized value _ _ _ =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .initialized binder.1 binder.2.1 binder.2.2
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, child, generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simp [Items.bindings, member])) tail)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly binder.2.1)
  | discard child generated remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | expression value =>
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .discard (lookupExpression?_complete unique contains)
            (children ⟨_, _, _, child, generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa [Items.bindings] using member)) tail)
  | assigning => cases closed
  | assigned remaining receipt targetType ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨_, _, value, _⟩ :=
            ScopedSourceForItemsAdmission.assignment_facts receipt.declaration targetType receipt.bare assignment
          obtain ⟨node, contains, same⟩ := value.stored_type
          exact .assign receipt.declaration targetType receipt.sourceProfile receipt.bare
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)

  | projectedAssigned remaining receipt route ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨_, _, value, _⟩ :=
            ScopedSourceForItemsAdmission.projected_assignment_facts unique receipt.description.binding route assignment
          obtain ⟨node, contains, same⟩ := value.stored_type
          refine .assignProjected receipt.description.binding route receipt.sourceProfile receipt.projected ?_
            (lookupExpression?_complete unique contains) same
            (children ⟨_, _, _, receipt.child, receipt.generated⟩ (by simp [Items.children]))
            (ih closed (fun child member => children child (by simp [Items.children, member]))
              (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)
          intro key member
          rw [← receipt.keyIds, ← keyChildren_ids receipt.keysGenerated] at member
          obtain ⟨child, present, same⟩ := List.mem_map.mp member
          subst key
          exact children child (by simp [Items.children, present])

  | bitNotting => cases closed
  | bitNotted remaining receipt targetType ih =>
      cases typed with
      | cons head tail =>
        exact .bitNot receipt.declaration targetType receipt.sourceProfile receipt.bare
          (ih closed (fun child member => children child (by simpa only [Items.children] using member))
            (fun binding member => bindings binding (by simpa only [Items.bindings] using member)) tail)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
