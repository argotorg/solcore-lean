import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates

/-! Exact-step direct-call extraction from the accepted contextual compiler.
Only the special-hook result at the actual recursive child and fuel is used.
The receipt retains the original node, full selected row and ordered actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual ordinary branch needs a single successful special-hook bypass
at this occurrence. No statement about other callbacks or budgets is required. -/
theorem of_supported
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (ordinary : Supported compilation.plan instantiation)
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation (Child policy body fuel compilation)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered) := by
  have original := accepted
  have originalSpecial := special
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨index, signature, specialized, codes, selected, record, arity, generated,
        parameter, result, emitted, output⟩ := NamedCalls.Arguments.call_of_accepted
          owner found read form originalSpecial original
      exact ⟨⟨node, output.symm ▸ Metadata.of_read metadata, form, ordinary, original, signature,
        index, specialized, (NamedCalls.selected_signature_target selected).1,
        (NamedCalls.selected_signature_target selected).2, record, arity, codes, generated, parameter,
        result.trans output.symm, emitted⟩⟩
  · simp [owner, bind, Except.bind] at accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedDirectExpressionReceipt
