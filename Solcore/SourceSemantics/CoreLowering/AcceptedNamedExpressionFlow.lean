import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedHeaderRootPolicyReceipts
import Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt

/-! Expression receipts start with the actual selected special-hook result.
The original source occurrence and minimum child budget remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

abbrev specialAction (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) :=
  match policy.lowerSpecial? with
  | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
  | some lower => lower context (Child policy body fuel context) (fuel + 1) source scope id reasonAt

/-- The selected hook is observed at its actual arguments. A successful override
retains its exact result, without any assumption about other child actions. -/
structure Head (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word)
    (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  owner : id.occurrence.owner = source.owner
  special : Option SourceCoreBasic.LoweredExpr
  selected : specialAction policy body fuel context source scope id reasonAt = .ok special
  result : ∀ actual, special = some actual → lowered = actual
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    context source scope id reasonAt = .ok lowered

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem Head.of_accepted
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      context source scope id reasonAt = .ok lowered) :
    Nonempty (Head policy body fuel context source scope id reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
    cases found : source.lookupExpression? id with
    | none => simp [found, bind, Except.bind] at accepted
    | some node =>
      simp only [found, bind, Except.bind, pure, Except.pure] at accepted
      cases hook : policy.lowerSpecial? with
      | none =>
        refine ⟨⟨node, found, owner, none, ?_, ?_, original⟩⟩
        · simp [specialAction, hook]
        · intro actual same
          cases same
      | some lower =>
        cases selected : lower context (Child policy body fuel context) (fuel + 1)
            source scope id reasonAt with
        | error error =>
          simp only [hook, selected] at accepted
          cases accepted
        | ok special =>
          refine ⟨⟨node, found, owner, special, ?_, ?_, original⟩⟩
          · simpa only [specialAction, hook] using selected
          · intro actual same
            rw [same] at selected
            simp only [hook, selected] at accepted
            exact (Except.ok.inj accepted).symm
  · simp [owner, bind, Except.bind] at accepted

/-- The actual contextual action exposes the same head after its genuine
predecessor budget has been recovered by the Header receipt. -/
theorem of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      ∃ root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
        (compiled := compiled) prepared.named prepared.diagnostics prepared.code prepared.compilation
        predecessor source scope id header.reasonAt lowered,
      Nonempty (Head root.selected.policy root.selected.lowerBody predecessor
        (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
        source scope id header.reasonAt lowered) := by
  obtain ⟨predecessor, same, ⟨root⟩⟩ :=
    CallableIndexedOwnedPreparedHeaderRootPolicyReceipts.at_accepted prepared aligned accepted
  exact ⟨predecessor, same, root, Head.of_accepted root.selected.accepted⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
