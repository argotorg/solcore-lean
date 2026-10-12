import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources

/-! A Source body whose complete occurrence table has no lambda can only use
a named invocation scope. Actual finite-plan owner uniqueness identifies its
sidecar and original guard frame, including after arbitrary attempted anonymous
selection. No invocation or expression execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFreeSelectedScopes
open Frontend SourceInference SourceCoreStageContracts

/-- Original, substituted and rewritten factory origins all retain an actual
lambda occurrence in the Source stored by the resulting closure. -/
theorem lambda_contains {plan : Plan} {owner : Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {function : Dynamic.Closure} {contract : Contract}
    (origin : CallableLedger.LambdaOrigin plan owner id active function contract) :
    ∃ identifier node, ContainsExpression function.source identifier node ∧
      node.form = .lambda function.parameters function.resultType function.body := by
  cases origin with
  | original prepared receipt samePlan sameOwner source parameters result body =>
    rw [source, parameters, result, body]
    exact ⟨_, _, CallContractCertificates.expression_sound receipt.selected, receipt.form⟩
  | contextual prepared receipt samePlan sameOwner source parameters result body =>
    rw [source, parameters, result, body]
    refine ⟨_, _, FlexibleSubstitution.ContainsExpression.applySubstitution _
      (CallContractCertificates.expression_sound receipt.selected), ?_⟩
    simp only [ExpressionNode.applySubstitution, receipt.form, ExpressionForm.applySubstitution]
  | applied recipe canonical retained samePlan sameOwner sameId source parameters result body =>
    rw [source, parameters, result, body]
    exact ⟨_, _, lookupExpression?_sound recipe.source_node, recipe.source_node_form⟩

/-- This is a finite original Source observation, independent of stage choice. -/
def NoLambda (source : TypedSource) : Prop :=
  ∀ id node, ContainsExpression source id node → ∀ parameters result body,
    node.form ≠ .lambda parameters result body

private theorem sidecar_member {plan : Plan} {key : Key} {sidecar : Sidecar}
    (issued : prepareSidecar plan key = .ok sidecar) : sidecar.caller ∈ plan.specializations := by
  have found := LambdaSourceAlignment.sidecar_lookup issued
  have filtered := CallableIndexedOwnedContextualDiagnosticSources.selected_filter found
  have member : sidecar.caller ∈ plan.specializations.filter
      (fun row => decide (row.key = key)) := by
    rw [filtered]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp member).1

/-- Genuine named selection provides both the exact original Source view and
its actual guard frame. Owner uniqueness is a checked finite-plan condition. -/
theorem selected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (key : Key) {function : Dynamic.Closure} {child : Staging.Recursive.Scope}
    (noLambda : NoLambda function.source)
    (uniqueOwner : ∀ row ∈ compiled.indexed.base.plan.specializations,
      row.function.typedBody.owner = function.source.owner → row.key = key)
    (selection : (RecursiveNamedPreparedStageScopes.registry actual).Closure function child) :
    ∃ sidecar,
      prepareSidecar compiled.indexed.base.plan key = .ok sidecar ∧
      CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source function.source ∧
      child.guards = CallableLedger.frame sidecar := by
  cases selection with
  | anonymous receipt =>
    cases receipt with
    | lambda prepared site source owner origin =>
      obtain ⟨id, node, present, form⟩ := lambda_contains origin
      exact False.elim (noLambda id node present _ _ _ form)
    | applied recipe sameProgram samePlan sameTable prepared sameOwner site source owner origin =>
      obtain ⟨id, node, present, form⟩ := lambda_contains origin
      exact False.elim (noLambda id node present _ _ _ form)
  | @named row prepared sidecar issued same =>
    have original : prepared.view.source = row.function.typedBody :=
      congrArg (fun row => row.function.typedBody) prepared.same
    have member : row ∈ compiled.indexed.base.plan.specializations := same ▸ sidecar_member issued
    have keyEq := uniqueOwner row member (congrArg TypedSource.owner original.symm)
    refine ⟨sidecar, ?_, Or.inl ?_, rfl⟩
    · simpa only [keyEq] using issued
    · exact original.trans (congrArg (fun row => row.function.typedBody) same.symm)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFreeSelectedScopes
