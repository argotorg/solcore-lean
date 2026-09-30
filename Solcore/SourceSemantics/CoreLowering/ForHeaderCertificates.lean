import Solcore.SourceSemantics.CoreLowering.ForHeaderTree
import Solcore.SourceSemantics.CoreLowering.LoopStatementCertificates

/-! Recover a static default header tree from actual compiler success. The
continuation hypothesis authenticates successful continuation code using only
its static scope/context alignment; no evaluation premise is accepted. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements
open LoopStatements.Default

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok
    {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

theorem tree_of_lowerForItems
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {site : SourceCoreElaboration.ErrorSite} {code : Core.Expr}
    {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Core.Expr}
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (nextCertificate : ∀ {scope context code}, ScopeContextAligned scope context →
      next scope = .ok code → continuation scope context code)
    (accepted : SourceCoreLoops.lowerForItems (defaultPolicy compilation) site fuel source scope items type reasonAt next = .ok code) :
    Tree compilation source reasonAt type continuation scope context items code := by
  induction fuel generalizing scope context items code with
  | zero =>
    cases items with
    | nil => exact .nil (nextCertificate aligned accepted)
    | cons => cases accepted
  | succ fuel ih =>
    cases items with
    | nil => exact .nil (nextCertificate aligned accepted)
    | cons item rest =>
      simp only [SourceCoreLoops.lowerForItems, defaultPolicy] at accepted
      cases item with
      | letDecl binder initializer =>
        obtain ⟨payload, binding, accepted⟩ := bind_ok accepted
        have certificate := lowerBinder_certificate binding
        have extension := certificate.extends aligned
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        have tail := ih (aligned.bind binder payload) compiledBody
        cases initializer with
        | none => cases accepted; exact .letUninitialized certificate extension tail
        | some initializer =>
          obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
          obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
          cases checkedUnit
          cases accepted
          obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
          rw [← ensureType_ok checked] at valueTree
          exact .letInitialized certificate extension valueTree tail
      | expression expression =>
        obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
        exact .discard valueTree (ih aligned compiledBody)
      | assignValue assignment operator rhs =>
        obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
        let assignmentStep := fun operator => do
          let (index, payload) ← SourceCoreBasic.lowerAssignment source scope assignment operator
          let value ← SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope rhs reasonAt
          SourceCoreBasic.ensureType (.binder assignment.target.root) payload value.type
          pure (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) value.expression body)
        change (match operator, (defaultPolicy compilation).assignValue with
          | .equal, _ | _, none => assignmentStep operator
          | _, some callback => callback (defaultPolicy compilation).lowerExpression fuel source scope site
              assignment operator rhs (Core.LocalLoop.controlType type) body reasonAt) = .ok code at accepted
        cases operator <;> dsimp only [defaultPolicy, assignmentStep] at accepted
        all_goals
          obtain ⟨⟨index, payload⟩, target, accepted⟩ := bind_ok accepted
          have certificate := lowerAssignment_certificate target
          have equal := certificate.equal
          cases equal
        obtain ⟨value, compiledValue, accepted⟩ := bind_ok accepted
        obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
        cases checkedUnit
        cases accepted
        obtain ⟨_, _, valueTree⟩ := PrimitiveExpressions.tree_of_lowerExpression unique compiledValue
        rw [← ensureType_ok checked] at valueTree
        exact .assign certificate valueTree (ih aligned compiledBody)
      | assignBitNot assignment => cases accepted

theorem tree_of_lowerPost
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {site : SourceCoreElaboration.ErrorSite} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerForItems (defaultPolicy compilation) site fuel source scope items type reasonAt
      (fun _ => .ok (Core.LocalLoop.fallthrough type)) = .ok code) :
    Tree compilation source reasonAt type (Fallthrough type) scope context items code :=
  tree_of_lowerForItems aligned unique (fun _ accepted => Except.ok.inj accepted.symm) accepted

end Solcore.SourceSemantics.CoreLowering.ForHeaders
