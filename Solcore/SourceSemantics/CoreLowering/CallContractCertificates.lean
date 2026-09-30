import Solcore.SourceSemantics.CoreLowering.CallStageBoundary
import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy

/-! Static provenance of retained callable contracts and call guards. These
lemmas inspect the actual metadata factories. They do not evaluate source/Core
code or infer source staging flags from projected Core function types.
Contextual lambda receipts retain the entire authenticated substitution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallContractCertificates
open Frontend Frontend.SourceInference SourceCoreStageContracts

abbrev SourceContract := Staging.CallGuard.Contract

def semanticContract (contract : Contract) : SourceContract :=
  ⟨contract.parameters, contract.stagedResult⟩

theorem expression_sound {sidecar : Sidecar} {id : ExpressionId} {node : ExpressionNode}
    (accepted : expression sidecar id = .ok node) : ContainsExpression sidecar.source id node := by
  unfold expression at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next selected found =>
      cases accepted
      have member : node ∈ [node] := List.mem_singleton_self _
      rw [← found] at member
      obtain ⟨candidate, member, selected⟩ := List.mem_filterMap.mp member
      cases candidate with
      | statement => cases selected
      | expression candidate =>
        by_cases same : candidate.id = id
        · simp only [same, ↓reduceIte, Option.some.injEq] at selected
          subst candidate
          exact ⟨member, same⟩
        · simp only [same, ↓reduceIte] at selected
          cases selected
    · cases accepted

/-- The factory's singleton check authenticates every matching occurrence,
not just the first-match lookup used by other frontend traversals. -/
theorem expression_unique {sidecar : Sidecar} {id : ExpressionId} {node other : ExpressionNode}
    (accepted : expression sidecar id = .ok node) (contains : ContainsExpression sidecar.source id other) :
    other = node := by
  unfold expression at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next selected found =>
      cases accepted
      have member : other ∈ sidecar.source.nodes.filterMap (fun
          | .expression candidate => if candidate.id = id then some candidate else none
          | .statement _ => none) := by
        apply List.mem_filterMap.mpr
        exact ⟨.expression other, contains.1, by simp only [contains.2, ↓reduceIte]⟩
      have sameFilter : (sidecar.source.nodes.filterMap (fun
          | .expression candidate => if candidate.id = id then some candidate else none
          | .statement _ => none)) = [node] := by
        refine Eq.trans ?_ found
        apply congrArg (fun (select : Node → Option ExpressionNode) => sidecar.source.nodes.filterMap select)
        funext item
        cases item with
        | expression candidate => by_cases same : candidate.id = id <;> simp [same]
        | statement => rfl
      rw [sameFilter] at member
      exact List.mem_singleton.mp member
    · cases accepted

private theorem exactSpecialization_key {plan : Plan} {key : Key} {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok caller) : caller.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have member : caller ∈ [caller] := List.mem_singleton_self _
    rw [← found] at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · cases accepted

theorem sidecar_of_accepted {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) : sidecar.plan = plan ∧ sidecar.caller.key = key := by
  unfold prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; exact ⟨rfl, exactSpecialization_key selected⟩
        · cases accepted

structure NamedReceipt (plan : Plan) (key : Key) (contract : Contract) where
  sidecar : Sidecar
  prepared : prepareSidecar plan key = .ok sidecar
  parameters : contract.parameters = sidecar.source.inputs
  stagedResult : contract.stagedResult =
    (sidecar.caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly sidecar.caller.function.inferredBodyType)
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan

theorem named_of_accepted {plan : Plan} {key : Key} {contract : Contract}
    (accepted : Contract.named plan key = .ok contract) : Nonempty (NamedReceipt plan key contract) := by
  unfold Contract.named at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · next sidecar prepared => cases accepted; exact ⟨⟨sidecar, prepared, rfl, rfl, rfl, rfl⟩⟩

structure LambdaReceipt (sidecar : Sidecar) (id : ExpressionId) (contract : Contract) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  selected : expression sidecar id = .ok node
  form : node.form = .lambda parameters result body
  parameters_eq : contract.parameters = parameters
  stagedResult : contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly result
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan

theorem lambda_of_accepted {sidecar : Sidecar} {id : ExpressionId} {contract : Contract}
    (accepted : Contract.lambda sidecar id = .ok contract) : Nonempty (LambdaReceipt sidecar id contract) := by
  unfold Contract.lambda at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · next node selected =>
    split at accepted
    · next parameters result body form =>
      split at accepted
      · cases accepted
      · cases accepted; exact ⟨⟨node, parameters, result, body, selected, form, rfl, rfl, rfl, rfl⟩⟩
    · cases accepted

structure ContextualLambdaReceipt (sidecar : Sidecar) (prepared : SourceCoreLocalEvidence.Prepared)
    (id : ExpressionId) (contract : Contract) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  selected : expression sidecar id = .ok node
  form : node.form = .lambda parameters result body
  parameters_eq : contract.parameters = parameters.map (TypedBinder.applySubstitution prepared.substitution)
  stagedResult : contract.stagedResult = SourceCompilationPlan.sourceTypeIsComptimeOnly (prepared.substitution.apply result)
  owner : contract.owner = sidecar.caller.key
  plan_eq : contract.plan = sidecar.plan
  caller_checked : (prepared.caller == { sidecar.caller with function := { sidecar.caller.function with
    typedBody := sidecar.source.applySubstitution prepared.substitution
    solvedRequirements := SourceCoreLocalEvidence.rewriteLedger prepared.substitution
      prepared.witnesses sidecar.caller.function.solvedRequirements } }) = true

theorem contextualLambda_of_accepted {sidecar : Sidecar} {prepared : SourceCoreLocalEvidence.Prepared}
    {id : ExpressionId} {contract : Contract}
    (accepted : Contract.contextualLambda sidecar prepared id = .ok contract) :
    Nonempty (ContextualLambdaReceipt sidecar prepared id contract) := by
  unfold Contract.contextualLambda at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · next caller =>
    split at accepted
    · cases accepted
    · next node selected =>
      split at accepted
      · next parameters result body form =>
        split at accepted
        · cases accepted
        · cases accepted
          refine ⟨⟨node, parameters, result, body, selected, form, rfl, rfl, rfl, rfl, ?_⟩⟩
          exact caller
      · cases accepted
  · cases accepted

structure GuardReceipt (sidecar : Sidecar) (call : ExpressionId) (contract : Contract) (guard : Guard) where
  sidecar_eq : guard.sidecar = sidecar
  contract_eq : guard.contract = contract
  selected : expression sidecar call = .ok guard.node
  callee : ExpressionId
  metadata : IndirectCallResolution
  form : guard.node.form = .call callee guard.arguments (.indirect metadata)

theorem guard_of_accepted {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    (accepted : prepareGuard sidecar call contract = .ok guard) :
    Nonempty (GuardReceipt sidecar call contract guard) := by
  unfold prepareGuard at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · split at accepted
    · cases accepted
    · next node selected =>
      split at accepted
      · next callee arguments metadata form =>
        cases accepted; exact ⟨⟨rfl, rfl, selected, callee, metadata, form⟩⟩
      · cases accepted
  · cases accepted

theorem GuardReceipt.call {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    (receipt : GuardReceipt sidecar call contract guard) : guard.node.id = call :=
  (expression_sound receipt.selected).2

theorem guard_arguments {sidecar : Sidecar} {call : ExpressionId} {contract : Contract} {guard : Guard}
    {node : ExpressionNode} {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (accepted : prepareGuard sidecar call contract = .ok guard)
    (contains : ContainsExpression sidecar.source call node)
    (form : node.form = .call callee arguments (.indirect metadata)) : guard.arguments = arguments := by
  obtain ⟨receipt⟩ := guard_of_accepted accepted
  have same := expression_unique receipt.selected contains
  have forms := receipt.form.symm.trans (same ▸ form)
  cases forms
  rfl

end Solcore.SourceSemantics.CoreLowering.CallContractCertificates
