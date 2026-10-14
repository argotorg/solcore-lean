import Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt

/-! Actual compiler receipts for for-loop header items. Each header retains
its exact continuation action, final lexical scope and generated expression
children. Unsupported item forms remain an explicit original-source boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

/-- Ordered expanded expression actions, including repeated source occurrences. -/
structure Child (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (reasonAt : ExpressionId → Word) where
  fuel : Nat
  scope : SourceCoreLocalCell.Scope
  expression : ExpressionId
  lowered : SourceCoreBasic.LoweredExpr
  accepted : policy.lowerExpression fuel source scope expression reasonAt = .ok lowered

structure Binding (policy : SourceCoreLoops.Policy) (source : TypedSource) where
  scope : SourceCoreLocalCell.Scope
  binder : TypedBinder
  payload : Ty
  projected : policy.lowerBinder source scope binder = .ok payload

/-- Bare value writes retain the original declaration type as well as native layout. -/
def Assignable (source : TypedSource) (assignment : AssignmentResolution)
    (operator : Solcore.Syntax.ValueAssignOp) : Prop :=
  (operator = .equal ∨ assignment.target.type = .word) ∧ assignment.target.projections = [] ∧
    ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
      binder.scheme.body = assignment.target.type

def HeaderForms (items : List ForItemForm) : Prop :=
  ∀ item ∈ items, ∀ assignment, item ≠ .assignBitNot assignment

inductive Items (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (result : Ty) (reasonAt : ExpressionId → Word)
    (next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr)
    (finalScope : SourceCoreLocalCell.Scope) (finish : Expr) :
    Nat → SourceCoreLocalCell.Scope → List ForItemForm → Expr → Type where
  | nil {fuel scope} (same : scope = finalScope) (accepted : next scope = .ok finish) :
      Items policy source site result reasonAt next finalScope finish fuel scope [] finish
  | absent {fuel scope binder payload rest tail code}
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (remaining : Items policy source site result reasonAt next finalScope finish fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letUninitialized policy.sourceCells source scope Renaming.id binder payload tail = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.letDecl binder none :: rest) code
  | initialized {fuel scope binder expression payload rest tail code}
      (projected : policy.lowerBinder source scope binder = .ok payload)
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (childType : SourceCoreBasic.ensureType (.binder binder.id) payload child.type = .ok ())
      (remaining : Items policy source site result reasonAt next finalScope finish fuel ((binder.id, payload) :: scope) rest tail)
      (allocated : SourceCoreSourceCells.letInitialized policy.sourceCells source scope Renaming.id binder
        (LocalLoop.controlType result) payload child.expression tail = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.letDecl binder (some expression) :: rest) code
  | discard {fuel scope expression rest tail}
      (child : SourceCoreBasic.LoweredExpr)
      (generated : policy.lowerExpression fuel source scope expression reasonAt = .ok child)
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.expression expression :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) child.expression tail)
  | assigning {fuel scope assignment operator expression rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator expression
        (LocalLoop.controlType result) tail reasonAt = .ok code) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignValue assignment operator expression :: rest) code
  | assigned {fuel scope assignment operator expression rest tail code}
      (remaining : Items policy source site result reasonAt next finalScope finish fuel scope rest tail)
      (receipt : AcceptedBareAssignmentReceipt.Receipt policy fuel source scope site assignment operator expression
        (LocalLoop.controlType result) tail reasonAt code)
      (targetType : receipt.binder.scheme.body = assignment.target.type) :
      Items policy source site result reasonAt next finalScope finish (fuel + 1) scope (.assignValue assignment operator expression :: rest) code

namespace Items
variable {policy : SourceCoreLoops.Policy} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {result : Ty} {reasonAt : ExpressionId → Word}
  {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
  {finalScope : SourceCoreLocalCell.Scope} {finish : Expr}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm} {code : Expr}

theorem of_accepted (forms : HeaderForms items)
    (accepted : SourceCoreLoops.lowerForItems policy site fuel source scope items result reasonAt next = .ok code) :
    ∃ finalScope finish, Nonempty (Items policy source site result reasonAt next finalScope finish fuel scope items code) := by
  induction fuel generalizing scope items code with
  | zero =>
    cases items with
    | nil => exact ⟨scope, code, ⟨.nil rfl accepted⟩⟩
    | cons item rest => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact ⟨scope, code, ⟨.nil rfl accepted⟩⟩
    | cons item rest =>
      have tailForms : HeaderForms rest := fun item member => forms item (List.mem_cons_of_mem _ member)
      cases item with
      | letDecl binder initializer =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
        obtain ⟨tail, generatedTail, accepted⟩ := bind_ok accepted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        cases initializer with
        | none => exact ⟨finalScope, finish, ⟨.absent projected remaining accepted⟩⟩
        | some expression =>
          obtain ⟨child, generated, accepted⟩ := bind_ok accepted
          obtain ⟨checked, childType, allocated⟩ := bind_ok accepted
          cases checked
          exact ⟨finalScope, finish, ⟨.initialized projected child generated childType remaining allocated⟩⟩
      | expression expression =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨child, generated, accepted⟩ := bind_ok accepted
        obtain ⟨tail, generatedTail, emitted⟩ := bind_ok accepted
        cases emitted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        exact ⟨finalScope, finish, ⟨.discard child generated remaining⟩⟩
      | assignValue assignment operator expression =>
        simp only [SourceCoreLoops.lowerForItems] at accepted
        obtain ⟨tail, generatedTail, assigned⟩ := bind_ok accepted
        obtain ⟨finalScope, finish, ⟨remaining⟩⟩ := ih tailForms generatedTail
        exact ⟨finalScope, finish, ⟨.assigning remaining assigned⟩⟩
      | assignBitNot assignment => exact False.elim (forms _ List.mem_cons_self assignment rfl)

theorem accepted (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    SourceCoreLoops.lowerForItems policy site fuel source scope items result reasonAt next = .ok code := by
  induction tree with
  | @nil fuel scope same accepted => cases fuel <;> exact accepted
  | absent projected remaining allocated ih =>
    simpa [SourceCoreLoops.lowerForItems, projected, ih, bind, Except.bind] using allocated
  | initialized projected child generated childType remaining allocated ih =>
    simpa [SourceCoreLoops.lowerForItems, projected, ih, generated, childType, bind, Except.bind] using allocated
  | discard child generated remaining ih =>
    simp [SourceCoreLoops.lowerForItems, generated, ih, bind, Except.bind, pure, Except.pure]
  | assigning remaining assigned ih =>
    simpa only [SourceCoreLoops.lowerForItems, ih, bind, Except.bind] using assigned
  | assigned remaining receipt targetType ih =>
    simpa only [SourceCoreLoops.lowerForItems, ih, bind, Except.bind] using receipt.accepted

theorem finish_accepted (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    next finalScope = .ok finish := by
  induction tree with
  | nil same accepted => exact same ▸ accepted
  | absent _ _ _ ih | initialized _ _ _ _ _ _ ih | discard _ _ _ ih
      | assigning _ _ ih | assigned _ _ _ ih => exact ih

def closed {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Bool :=
  match tree with
  | .nil .. => true
  | .absent _ remaining _ | .initialized _ _ _ _ remaining _ | .discard _ _ remaining | .assigned remaining _ _ => remaining.closed
  | .assigning .. => false

def children {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : List (Child policy source reasonAt) :=
  match tree with
  | .nil .. => []
  | .absent _ remaining _ | .assigning remaining _ => remaining.children
  | @Items.initialized _ _ _ _ _ _ _ _ fuel scope _ expression _ _ _ _ _ child generated _ remaining _ =>
      ⟨fuel, scope, expression, child, generated⟩ :: remaining.children
  | @Items.discard _ _ _ _ _ _ _ _ fuel scope expression _ _ child generated remaining =>
      ⟨fuel, scope, expression, child, generated⟩ :: remaining.children
  | @Items.assigned _ _ _ _ _ _ _ _ fuel scope _ _ expression _ _ _ remaining receipt _ =>
      ⟨fuel, scope, expression, receipt.child, receipt.generated⟩ :: remaining.children

def bindings {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : List (Binding policy source) :=
  match tree with
  | .nil .. => []
  | @Items.absent _ _ _ _ _ _ _ _ _ scope binder payload _ _ _ projected remaining _ =>
      ⟨scope, binder, payload, projected⟩ :: remaining.bindings
  | @Items.initialized _ _ _ _ _ _ _ _ _ scope binder _ payload _ _ _ projected _ _ _ remaining _ =>
      ⟨scope, binder, payload, projected⟩ :: remaining.bindings
  | .discard _ _ remaining | .assigning remaining _ | .assigned remaining _ _ => remaining.bindings

def Ready {fuel scope items code} (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) : Prop :=
  match tree with
  | .nil .. => True
  | .absent _ remaining _ | .initialized _ _ _ _ remaining _ | .discard _ _ remaining | .assigned remaining _ _ => remaining.Ready
  | @Items.assigning _ _ _ _ _ _ _ _ _ _ assignment operator _ _ _ _ remaining _ =>
      ¬ Assignable source assignment operator ∧ remaining.Ready

theorem refine {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    (matched : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (tree : Items policy source site result reasonAt next finalScope finish fuel scope items code) :
    ∃ refined : Items policy source site result reasonAt next finalScope finish fuel scope items code, refined.Ready := by
  classical
  induction tree with
  | nil same accepted => exact ⟨.nil same accepted, True.intro⟩
  | absent projected remaining allocated ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.absent projected tail allocated, ready⟩
  | initialized projected child generated childType remaining allocated ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.initialized projected child generated childType tail allocated, ready⟩
  | discard child generated remaining ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.discard child generated tail, ready⟩
  | @assigning fuel scope assignment operator expression rest tail code remaining assigned ih =>
    obtain ⟨remaining, ready⟩ := ih
    by_cases supported : Assignable source assignment operator
    · obtain ⟨profile, bare, type⟩ := supported
      obtain ⟨receipt⟩ := AcceptedBareAssignmentReceipt.of_accepted matched profile bare assigned
      exact ⟨.assigned remaining receipt (type receipt.binder receipt.declaration), ready⟩
    · exact ⟨.assigning remaining assigned, supported, ready⟩
  | assigned remaining receipt targetType ih =>
    obtain ⟨tail, ready⟩ := ih
    exact ⟨.assigned tail receipt targetType, ready⟩

end Items
end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
