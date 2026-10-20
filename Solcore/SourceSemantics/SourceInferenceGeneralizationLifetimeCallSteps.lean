import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeCallSuffix
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps
import Solcore.SourceSemantics.SourceInferenceExpressionCallProvenance
import Solcore.SourceSemantics.SourceInferenceActualIndirectCallPrefix

/-! The actual dispatch after a call's arguments preserves generalizations
created in those arguments or in its indirect callee. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem indirect_callee_suffix
    {entryNext : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {id : ExpressionId} {arguments : List InferredExpression} {expected : Option Ty}
    {callee : InferredExpression} {state : State} {application : IndirectApplicationResult}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (calleeBelow : callee.type.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (argumentsBefore : ∀ argument ∈ arguments, argument.type.VariablesBelow entryNext)
    (expectedBefore : ∀ type ∈ expected, type.VariablesBelow entryNext)
    (applicationAccepted : applyFunctionType context id callee.type arguments expected state = .ok application)
    (recorded : recordIndirectCall source callee arguments application = result)
    (lifetime : GeneralizationLifetime event entryNext state [callee.type]) :
    GeneralizationLifetime event entryNext result.2 [result.1.type] := by
  have after := lifetime.applyIndirect catalog.catalog ready calleeBelow argumentsBelow expectedBelow
    (lifetime.values _ (by simp))
    (fun argument member => lifetime.older _ (argumentsBefore argument member))
    (fun type member => lifetime.older _ (expectedBefore type member)) applicationAccepted
  have properties := applyFunctionType_inferenceProperties ready calleeBelow argumentsBelow expectedBelow applicationAccepted
  have completed := after.recordIndirect source callee arguments properties.2.1 properties.2.2
    (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
  rw [recorded] at completed
  exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem call_arguments_suffix
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have properties := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have expectedAfter : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (expectedBelow type member).weaken properties.1.next_le
  have argumentsSafe : ∀ argument ∈ child.1, Safe binder.scheme.quantified child.2 argument.type :=
    fun argument member => lifetime.values _ (List.mem_map.mpr ⟨argument, member, rfl⟩)
  have expectedSafe : ∀ type ∈ expected, Safe binder.scheme.quantified child.2 type :=
    fun type member => lifetime.older _ (expectedBelow type member)
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have after := lifetime.selectCandidate catalog origin.candidatesSubset properties.2.1 properties.2.2
        expectedAfter argumentsSafe expectedSafe selected
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties properties.2.1 properties.2.2
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (origin.candidatesSubset member) (catalog.canonical signature (origin.candidatesSubset member)) _)
        expectedAfter selected
      have completed := after.recordSelected source callee name inferredArguments selectedProperties.2.1 selectedProperties.2.2
        (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [recorded] at completed
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  | builtin _ actualArguments recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have completed := lifetime.recordBuiltin properties.2.1 properties.2.2 expectedAfter argumentsSafe expectedSafe recorded
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
      have same := Except.ok.inj (actualArguments.symm.trans childAccepted)
      cases same
      have calleeProperties := inferExprFuel_inferenceProperties properties.2.1 catalog.formation catalog.canonical (by simp) calleeAccepted
      have afterCallee := lifetime.inferExpr properties.2.1
        ((inferExprsFuel_direct_progress childAccepted).wellFormed wellFormed) catalog (by simp) (by simp) calleeAccepted
      have after := afterCallee.applyIndirect catalog.catalog calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le)
        (afterCallee.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
        (fun argument member => afterCallee.values _ (List.mem_append_left _ (List.mem_map.mpr ⟨argument, member, rfl⟩)))
        (fun type member => afterCallee.older _ (expectedBelow type member)) applicationAccepted
      have applicationProperties := applyFunctionType_inferenceProperties calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le) applicationAccepted
      have completed := after.recordIndirect source inferredCallee inferredArguments applicationProperties.2.1 applicationProperties.2.2
        (after.values _ (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [recorded] at completed
      exact completed.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem call_arguments
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok child)
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result)
    (lifetime : GeneralizationLifetime event allocated.inference.next child.2 (child.1.map (·.type))) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have allocatedWF : allocated.RequirementsWellFormed := by rw [allocatedEq]; exact wellFormed
  have after := lifetime.call_arguments_suffix (allocatedEq ▸ ready.allocateExpressionId) allocatedWF catalog
    (fun type member => sameNext ▸ expectedBelow type member) nonconstructor childAccepted
    (inferExprFuel_success_call_dispatch_provenance_facts form allocation accepted)
  simpa only [sameNext] using after

theorem call_callee
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial allocated argumentState calleeState : State}
    {inferredArguments : List InferredExpression} {inferredCallee : InferredExpression}
    {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .call callee arguments)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (nonconstructor : constructorCalleeCandidates context allocated callee = .ok [])
    (argumentsAccepted : inferExprsFuel fuel context arguments.elements allocated = .ok (inferredArguments, argumentState))
    (indirect : SourceInferenceExecution.IndirectCalleeAt context callee argumentState)
    (calleeAccepted : inferExprFuel fuel context callee none argumentState = .ok (inferredCallee, calleeState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok result)
    (lifetime : GeneralizationLifetime event argumentState.inference.next calleeState [inferredCallee.type]) :
    GeneralizationLifetime event initial.inference.next result.2 [result.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by rw [allocatedEq]; rfl
  have argumentsProperties := inferExprsFuel_inferenceProperties (allocatedEq ▸ ready.allocateExpressionId)
    catalog.formation catalog.canonical argumentsAccepted
  have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1
    catalog.formation catalog.canonical (by simp) calleeAccepted
  obtain ⟨application, applicationAccepted, recorded⟩ :=
    SourceInferenceExecution.indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect calleeAccepted accepted
  have before : initial.inference.next ≤ argumentState.inference.next := sameNext ▸ argumentsProperties.1.next_le
  have completed := lifetime.indirect_callee_suffix calleeProperties.2.1 catalog calleeProperties.2.2
    (fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le)
    (fun type member => (expectedBelow type member).weaken (Nat.le_trans before calleeProperties.1.next_le))
    argumentsProperties.2.2 (fun type member => (expectedBelow type member).weaken before)
    applicationAccepted recorded
  exact completed.weaken_entry before

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
