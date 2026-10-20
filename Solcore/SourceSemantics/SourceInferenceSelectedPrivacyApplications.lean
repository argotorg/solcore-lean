import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyArguments

/-! Indirect application follows both executable branches: fitting an exposed
function or allocating a real result variable and unifying a function type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) :
    type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

private theorem unify_requirements {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    rfl

/-- The caller supplies privacy of the actual callee, arguments and optional
expectation. The successful application itself supplies every continuation. -/
theorem applyFunctionType_private {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {state : State}
    {result : Detail.IndirectApplicationResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (calleeSafe : Safe protectedVars state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    SafeTransport protectedVars state result.state ∧
    Safe protectedVars result.state result.result.type ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  have argumentsBelow : ∀ type ∈ arguments.map InferredExpression.type,
      type.VariablesBelow state.inference.next := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsBelow arg argMember
  have argumentsSafe : ∀ type ∈ arguments.map InferredExpression.type,
      Safe protectedVars state type := by
    intro type member
    obtain ⟨arg, argMember, rfl⟩ := List.mem_map.mp member
    exact argumentsSafe arg argMember
  have productBelow := Ty.variablesBelow_productMany argumentsBelow
  have productSafe := safe_productMany protectedVars state _ argumentsSafe
  rcases Detail.applyFunctionType_success_facts accepted with existing | inferred
  · obtain ⟨parameter, returnType, fittedArgument, fittedResult, parts, argumentFit, resultFit, resultEq⟩ := existing
    subst result
    have partsBelow := Detail.functionParts?_success_variablesBelow
      (ready.solved.variablesBelow_apply calleeBelow) parts
    have partsSafe : Safe protectedVars state parameter ∧ Safe protectedVars state returnType := by
      have safe := safe_resolved ready calleeSafe
      rw [functionParts_eq parts] at safe
      exact (safe_function_iff _ _ _ _).mp safe
    have parameterBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact partsBelow.1
    have parameterSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact partsSafe.1
    have argumentProgress := Detail.withExpected_inferenceProperties ready productBelow parameterBelow argumentFit
    have argumentPrivacy := withExpected_private ready productBelow parameterBelow productSafe parameterSafe live argumentFit
    have argumentRows := withExpected_new_requirements_private catalog ready productSafe parameterSafe argumentFit
    have resultPrivacy := withExpected_private argumentProgress.2.1
      (partsBelow.2.weaken argumentProgress.1.next_le)
      (fun type member => (expectedBelow type member).weaken argumentProgress.1.next_le)
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member))
      argumentPrivacy.2.2 resultFit
    have resultRows := withExpected_new_requirements_private catalog argumentProgress.2.1
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member)) resultFit
    exact ⟨argumentPrivacy.1.trans resultPrivacy.1, resultPrivacy.2.1,
      resultPrivacy.2.2, new_requirements_trans argumentRows resultRows resultPrivacy.1⟩
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have freshProgress := State.InferenceProgress.fresh state ready.solved
    have freshReady := State.InferenceReady.fresh ready
    have freshSafe := fresh_type ready bound
    have freshTransport : SafeTransport protectedVars state state.fresh.2 := fresh
    have freshBelow : state.fresh.1.VariablesBelow state.fresh.2.inference.next := by
      change Ty.VariablesBelow (state.inference.next + 1) (.variable ⟨state.inference.next⟩)
      exact (Ty.variablesBelow_variable_iff _ _).mpr (Nat.lt_succ_self _)
    have freshBinders : state.fresh.2.localBinders = state.localBinders := rfl
    have freshRequirements : state.fresh.2.requirements = state.requirements := rfl
    rw [allocated] at freshProgress freshReady freshSafe freshTransport freshBelow freshBinders freshRequirements
    change freshState.requirements = state.requirements at freshRequirements
    have functionBelow := (Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨productBelow.weaken freshProgress.next_le, freshBelow⟩
    have functionSafe := (safe_function_iff protectedVars freshState _ _).mpr
      ⟨freshTransport _ productSafe, freshSafe⟩
    have unifyProgress := Detail.unify_inferenceProgress freshReady.solved
      (calleeBelow.weaken freshProgress.next_le) functionBelow unified
    have unifiedReady := Detail.unify_preserves_inferenceReady freshReady
      (calleeBelow.weaken freshProgress.next_le) functionBelow unified
    have unifyPrivacy := ProtectedVariables.unify (freshTransport _ calleeSafe) functionSafe unified
    have beforeFit := freshTransport.trans unifyPrivacy
    have nextLe := (freshProgress.trans unifyProgress).next_le
    have unifiedLive := (live.transport freshBinders freshTransport).transport
      (congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unified)) unifyPrivacy
    have resultPrivacy := withExpected_private unifiedReady
      (freshBelow.weaken unifyProgress.next_le)
      (fun type member => (expectedBelow type member).weaken nextLe)
      (unifyPrivacy _ freshSafe)
      (fun type member => beforeFit _ (expectedSafe type member)) unifiedLive resultFit
    have resultRows := withExpected_new_requirements_private catalog unifiedReady
      (unifyPrivacy _ freshSafe)
      (fun type member => beforeFit _ (expectedSafe type member)) resultFit
    refine ⟨beforeFit.trans resultPrivacy.1, resultPrivacy.2.1, resultPrivacy.2.2, ?_⟩
    intro row member newRow
    apply resultRows row member
    simpa only [unify_requirements unified, freshRequirements] using newRow

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
