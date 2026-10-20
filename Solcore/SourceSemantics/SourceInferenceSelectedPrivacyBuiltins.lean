import Solcore.SourceSemantics.SourceInferenceSelectedPrivacySignatureReferences

/-! Fixed builtin calls use their actual equal-argument unifications and
expected-result unification. They issue no requirement rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private theorem unify_requirements {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    rfl

private theorem equal_arguments_private {protectedVars : List TypeVarId}
    {arguments : List InferredExpression} {parameters : List Ty} {state result : State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok result) :
    SafeTransport protectedVars state result ∧ LiveBindersSafe protectedVars result ∧
      result.requirements = state.requirements := by
  induction arguments generalizing parameters state result with
  | nil =>
    simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
    subst result
    exact ⟨.refl _ _, live, rfl⟩
  | cons argument arguments ih =>
    cases parameters with
    | nil =>
      simp only [Detail.unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      subst result
      exact ⟨.refl _ _, live, rfl⟩
    | cons parameter parameters =>
      cases unified : Detail.unify state argument.type parameter with
      | error error => simp [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
      | ok middle =>
        simp only [Detail.unifyBuiltinFunctionArgumentsEqual, unified, bind, Except.bind] at accepted
        have argSafe := argumentsSafe argument List.mem_cons_self
        have paramSafe := parametersSafe parameter List.mem_cons_self
        have transport := ProtectedVariables.unify argSafe paramSafe unified
        have child := ih
          (fun arg member => transport _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
          (fun param member => transport _ (parametersSafe param (List.mem_cons_of_mem _ member)))
          (live.unify argSafe paramSafe unified) accepted
        exact ⟨transport.trans child.1, child.2.1, child.2.2.trans (unify_requirements unified)⟩

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

private theorem builtin_finish_private {protectedVars : List TypeVarId}
    (source callee : Syntax.Expr) (name : String) (function : BuiltinFunctionId)
    (arguments : List InferredExpression) (call : ExpressionId) (state : State)
    (live : LiveBindersSafe protectedVars state) :
    let result := builtin_finish source callee name function arguments call state
    SafeTransport protectedVars state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = state.requirements := by
  dsimp only
  have transport : SafeTransport protectedVars state
      (builtin_finish source callee name function arguments call state).2 := .of_substitution_eq rfl
  refine ⟨transport, ?_, live.transport rfl transport, rfl⟩
  have fixed : state.resolve function.returnType = function.returnType :=
    Ty.apply_eq_self_of_domain_disjoint_freeVariables _ _ (by
      intro metavariable _ occurs
      exact Nat.not_lt_zero _ (builtin_return_closed function metavariable occurs))
  change Safe protectedVars (builtin_finish source callee name function arguments call state).2
    (state.resolve function.returnType)
  rw [fixed]
  exact safe_closed _ _ (builtin_return_closed function)

/-- The actual builtin call checks introduce no fresh requirement identities
and preserve privacy through every performed unification. -/
theorem recordBuiltinFunctionCall_private {protectedVars : List TypeVarId}
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    SafeTransport protectedVars state result.2 ∧ Safe protectedVars result.2 result.1.type ∧
      LiveBindersSafe protectedVars result.2 ∧ result.2.requirements = state.requirements := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  by_cases arity : arguments.length = function.parameterTypes.length
  · simp only [if_pos arity, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases argumentsRun : Detail.unifyBuiltinFunctionArgumentsEqual arguments function.parameterTypes state with
    | error error => simp [argumentsRun] at accepted
    | ok argumentState =>
      simp only [argumentsRun] at accepted
      have argumentPrivacy := equal_arguments_private argumentsSafe
        (fun type member => safe_closed _ _ (builtin_parameters_closed function type member)) live argumentsRun
      cases expected with
      | none =>
        have same : builtin_finish source callee name function arguments call argumentState = result := by
          simpa only [builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
        subst result
        have complete := builtin_finish_private source callee name function arguments call argumentState argumentPrivacy.2.1
        exact ⟨argumentPrivacy.1.trans complete.1, complete.2.1, complete.2.2.1,
          complete.2.2.2.trans argumentPrivacy.2.2⟩
      | some expected =>
        cases resultRun : Detail.unify argumentState function.returnType expected with
        | error error => simp [resultRun] at accepted
        | ok finalState =>
          have same : builtin_finish source callee name function arguments call finalState = result := by
            simpa only [resultRun, builtin_finish, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] using accepted
          subst result
          have returnsSafe : Safe protectedVars argumentState function.returnType :=
            safe_closed _ _ (builtin_return_closed function)
          have expectedSafe := argumentPrivacy.1 _ (expectedSafe expected rfl)
          have transport := ProtectedVariables.unify returnsSafe expectedSafe resultRun
          have finalLive := argumentPrivacy.2.1.unify returnsSafe expectedSafe resultRun
          have complete := builtin_finish_private source callee name function arguments call finalState finalLive
          exact ⟨argumentPrivacy.1.trans (transport.trans complete.1), complete.2.1, complete.2.2.1,
            complete.2.2.2.trans ((unify_requirements resultRun).trans argumentPrivacy.2.2)⟩
  · simp [arity, bind, Except.bind] at accepted

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
