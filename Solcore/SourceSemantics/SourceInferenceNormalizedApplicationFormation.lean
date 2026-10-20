import Solcore.SourceSemantics.SourceInferenceNormalizedArgumentFormation

/-! Normalized formation follows the actual exposed-function and fresh-result
branches of indirect application. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) : type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) : after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The real call reveals both successful fits. Actual inference progress
places each fit under the final continuation; a fresh result is formed from
the finalizer's range rather than an assumed unification formation law. -/
theorem applyFunctionType_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {call : ExpressionId} {callee : Ty} {arguments : List InferredExpression}
    {expected : Option Ty} {state : State} {result : Detail.IndirectApplicationResult}
    (formation : FormationContext semantic context outer)
    (binders : TypeParameterBindersWellFormed semantic)
    (ready : state.InferenceReady)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeFormed : TypeAdmissible semantic (outer.apply callee))
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    TypeAdmissible semantic (outer.apply result.result.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have productBelow : (Ty.productMany (arguments.map InferredExpression.type)).VariablesBelow state.inference.next := by
    apply Ty.variablesBelow_productMany
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsBelow arg argMember
  have productFormed : TypeAdmissible semantic (outer.apply (Ty.productMany (arguments.map InferredExpression.type))) := by
    rw [FlexibleSubstitution.apply_productMany]
    apply TypeAdmissible.productMany binders
    intro type member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨argument, argumentMember, rfl⟩ := List.mem_map.mp originalMember
    exact argumentsFormed argument argumentMember
  rcases Detail.applyFunctionType_success_facts accepted with existing | inferred
  · obtain ⟨parameter, returnType, fittedArgument, fittedResult, parts, argumentFit, resultFit, resultEq⟩ := existing
    subst result
    have partsBelow := Detail.functionParts?_success_variablesBelow
      (ready.solved.variablesBelow_apply calleeBelow) parts
    have parameterBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact partsBelow.1
    have argumentProgress := Detail.withExpected_inferenceProperties ready productBelow parameterBelow argumentFit
    have resultProgress := Detail.withExpected_inferenceProperties argumentProgress.2.1
      (partsBelow.2.weaken argumentProgress.1.next_le)
      (fun type member => (expectedBelow type member).weaken argumentProgress.1.next_le) resultFit
    have argumentContinuation : outer.SemanticallyExtends fittedArgument.state.inference.substitution :=
      continuation.trans resultProgress.1.substitution_extends
    have entryContinuation : outer.SemanticallyExtends state.inference.substitution :=
      argumentContinuation.trans argumentProgress.1.substitution_extends
    have resolvedFormed : TypeAdmissible semantic (outer.apply (state.resolve callee)) :=
      (entryContinuation callee).symm ▸ calleeFormed
    rw [functionParts_eq parts] at resolvedFormed
    change TypeAdmissible semantic (.function (outer.apply parameter) (outer.apply returnType)) at resolvedFormed
    have parameterFormed : ∀ type ∈ some parameter, TypeAdmissible semantic (outer.apply type) := by
      intro type member
      cases Option.mem_def.mp member
      exact resolvedFormed.function_parameter
    have argumentFormation := withExpected_normalized_formation formation argumentContinuation
      productFormed parameterFormed argumentFit
    have resultFormation := withExpected_normalized_formation formation continuation
      resolvedFormed.function_result expectedFormed resultFit
    exact ⟨resultFormation.1, new_normalized_requirements_trans argumentFormation.2 resultFormation.2⟩
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have returnEq : returnType = .variable ⟨state.inference.next⟩ := by
      have eq := congrArg Prod.fst allocated
      exact eq.symm
    have returnFormed : TypeAdmissible semantic (outer.apply returnType) := by
      rw [returnEq]
      exact type_applySubstitution_residual formation.residual formation.range
        (.variableOfResidual binders formation.residual _)
    have resultFormation := withExpected_normalized_formation formation continuation returnFormed expectedFormed resultFit
    refine ⟨resultFormation.1, ?_⟩
    intro row member fresh
    apply resultFormation.2 row member
    rw [unify_requirements unified]
    have freshEq : freshState = state.fresh.2 := (congrArg Prod.snd allocated).symm
    simpa only [freshEq, State.fresh] using fresh

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
