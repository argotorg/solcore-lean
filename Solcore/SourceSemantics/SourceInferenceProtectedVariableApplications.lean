import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem functionParts_eq {type parameter result : Ty}
    (found : Detail.functionParts? type = some (parameter,result)) :
    type = .function parameter result := by
  cases type <;> simp [Detail.functionParts?] at found
  case function left right => rcases found with ⟨rfl,rfl⟩; rfl

theorem applyFunctionType_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {call : ExpressionId} {callee : Ty}
    {arguments : List InferredExpression} {expected : Option Ty} {state : State}
    {result : Detail.IndirectApplicationResult}
    (ready : state.InferenceReady)
    (bound : ∀ metavariable ∈ protectedVars, metavariable.index < state.inference.next)
    (calleeBelow : callee.VariablesBelow state.inference.next)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (calleeSafe : Safe protectedVars state callee)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.applyFunctionType context call callee arguments expected state = .ok result) :
    FixesProtected protectedVars result.state := by
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
    have argumentPrivacy := withExpected_private ready productBelow parameterBelow productSafe parameterSafe live argumentFit
    have argumentFixed := withExpected_fixes_protected fixed productSafe parameterSafe argumentFit
    exact withExpected_fixes_protected argumentFixed
      (argumentPrivacy.1 _ partsSafe.2)
      (fun type member => argumentPrivacy.1 _ (expectedSafe type member)) resultFit
  · obtain ⟨returnType, freshState, unifiedState, fittedResult, _, allocated, unified, resultFit, resultEq⟩ := inferred
    subst result
    have freshSafe := fresh_type ready bound
    have freshTransport : SafeTransport protectedVars state state.fresh.2 := fresh
    have freshFixed : FixesProtected protectedVars state.fresh.2 := fixed.of_substitution_eq rfl
    rw [allocated] at freshSafe freshTransport freshFixed
    have functionSafe := (safe_function_iff protectedVars freshState _ _).mpr
      ⟨freshTransport _ productSafe, freshSafe⟩
    have unifyPrivacy := ProtectedVariables.unify (freshTransport _ calleeSafe) functionSafe unified
    have unifiedFixed := unify_fixes_protected freshFixed (freshTransport _ calleeSafe) functionSafe unified
    exact withExpected_fixes_protected unifiedFixed
      (unifyPrivacy _ freshSafe)
      (fun type member => unifyPrivacy _ (freshTransport _ (expectedSafe type member))) resultFit

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
