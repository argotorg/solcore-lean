import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem equal_arguments_fixed {protectedVars : List TypeVarId}
    {arguments : List InferredExpression} {parameters : List Ty} {state result : State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    SafeTransport protectedVars state result ∧ FixesProtected protectedVars result := by
  induction arguments generalizing parameters state result with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, fixed⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      subst result
      exact ⟨.refl _ _, fixed⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
      | ok middle =>
        simp only [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
        have argumentSafe := argumentsSafe argument List.mem_cons_self
        have parameterSafe := parametersSafe parameter List.mem_cons_self
        have transport := ProtectedVariables.unify argumentSafe parameterSafe unified
        have child := ih
          (fun arg member => transport _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
          (fun param member => transport _ (parametersSafe param (List.mem_cons_of_mem _ member)))
          (unify_fixes_protected fixed argumentSafe parameterSafe unified) accepted
        exact ⟨transport.trans child.1, child.2⟩

private theorem builtin_parameters_closed (function : BuiltinFunctionId) :
    ∀ type ∈ function.parameterTypes, type.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.parameterTypes, Ty.integer, Ty.word]

private theorem builtin_return_closed (function : BuiltinFunctionId) :
    function.returnType.VariablesBelow 0 := by
  cases function <;> simp [BuiltinFunctionId.returnType, Ty.integer, Ty.word, Ty.bool]

private def builtin_finish (source callee : Syntax.Expr) (name : String)
    (function : BuiltinFunctionId) (arguments : List InferredExpression) (call : ExpressionId)
    (state : State) : InferredExpression × State :=
  let (calleeId, state) := state.allocateExpressionId
  let calleeExpression : InferredExpression := {id := calleeId, type := function.type}
  let (_, state) := Detail.recordExpression callee calleeExpression
    (.reference name (.builtinFunction function)) [] [] state
  let result : InferredExpression := {id := call, type := state.resolve function.returnType}
  Detail.recordExpression source result
    (.call calleeId (arguments.map (·.id)) (.builtinFunction function)) [] [] state

theorem recordBuiltinFunctionCall_fixes_protected {protectedVars : List TypeVarId}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    FixesProtected protectedVars result.2 := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases argumentsRun : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentsRun] at accepted
    | ok argumentState =>
      simp only [argumentsRun] at accepted
      have argumentFrame := equal_arguments_fixed argumentsSafe
        (fun type member => safe_closed _ _ (builtin_parameters_closed function type member)) fixed argumentsRun
      cases expected with
      | none =>
        have same : builtin_finish source callee name function arguments call argumentState = result := by
          simpa only [builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
        subst result
        exact argumentFrame.2.of_substitution_eq rfl
      | some expected =>
        cases resultRun : Detail.unify argumentState function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok finalState =>
          have same : builtin_finish source callee name function arguments call finalState = result := by
            simpa only [resultRun, builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
          subst result
          have finalFixed := unify_fixes_protected argumentFrame.2
            (safe_closed _ _ (builtin_return_closed function))
            (argumentFrame.1 _ (expectedSafe expected rfl)) resultRun
          exact finalFixed.of_substitution_eq rfl
  · simp [arity, bind, Except.bind] at accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
