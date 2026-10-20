import Solcore.Frontend.SourceInference.LocalReadOriginsProgress

/-! Inference helpers outside declaration candidate selection preserve the
exact direct-call requirement classification. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.DirectCallEvents
open TypeSystem Detail

abbrev Unchanged (before after : State) : Prop :=
  after.directCallRequirements = before.directCallRequirements
namespace Unchanged
theorem refl (state : State) : Unchanged state state := rfl
theorem trans {before middle after : State}
    (first : Unchanged before middle) (second : Unchanged middle after) :
    Unchanged before after := Eq.trans second first
theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Unchanged state (state.addRequirementWithId predicate).2 := rfl
theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Unchanged state (state.addRequirementsWithIds predicates).2 :=
  State.addRequirementsWithIds_direct_eq state predicates
end Unchanged
private theorem pureState_eq {state next : State}
    (accepted : (pure state : Except Error State) = .ok next) : state = next :=
  Except.ok.inj accepted

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type}
    (value result : alpha) : ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp

theorem unify_direct_unchanged {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Unchanged state next := by
  unfold unify at accepted
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at accepted
  cases accepted
  exact .refl _

theorem freshTypes_direct_unchanged (count : Nat) (state : State) :
    Unchanged state (freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact ih state.fresh.2

theorem freshDataConstructorInstantiation_direct_unchanged
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) (state : State) :
    Unchanged state (freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldProgress (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      Unchanged accumulator.2 (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl _
    | cons parameter parameters ih => exact ih (step accumulator parameter)
  exact foldProgress dataType.parameters ([], state)

theorem attachExpressionCoercions_direct_unchanged (state : State) (entries : List ExpressionCoercions) :
    Unchanged state (attachExpressionCoercions state entries) := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    exact ih (state.modifyExpressionNode entry.expression fun node => appendExpressionCoercions node entry.coercions)

theorem recordExpression_direct_unchanged
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    Unchanged state
      (recordExpression source expression form requirements coercions state localSchemeInstantiationStart).2 :=
  .refl _

theorem recordExpressionWithExpected_direct_unchanged
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State} {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) : Unchanged state result.2 :=
  recordExpressionWithExpected_direct_eq accepted

theorem recordSelectedCallResult_direct_unchanged
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    Unchanged state
      (recordSelectedCallResult source callee name arguments attempt result trailingCoercions state).2 :=
  attachExpressionCoercions_direct_unchanged state attempt.argumentCoercions

theorem recordSelectedCall_direct_unchanged
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Unchanged attempt.state (recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_direct_unchanged source callee name arguments attempt attempt.result [] attempt.state

theorem recordIndirectCall_direct_unchanged (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Unchanged result.state (recordIndirectCall source callee arguments result).2 := .refl _

theorem inferUnaryOperator_direct_unchanged
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Unchanged state result.state := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_unchanged (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact Unchanged.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _)
    | exact (unify_direct_unchanged (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_unchanged (state := state) (by assumption)).trans
        (unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _))

theorem inferBinaryOperator_direct_unchanged
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Unchanged state result.state := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_unchanged (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact Unchanged.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _)
    | exact (unify_direct_unchanged (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_unchanged (state := state) (by assumption)).trans
        (unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _))


private theorem fresh_direct_unchanged (state : State) :
    Unchanged state state.fresh.2 := .refl _

theorem applyFunctionType_direct_unchanged
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    Unchanged state result.state := by
  unfold applyFunctionType at success
  cases partsResult : functionParts? (state.resolve calleeType) with
  | some parts =>
      rcases parts with ⟨parameter, returnType⟩
      simp only [partsResult] at success
      cases argumentResult : withExpected context state
          { id := call, type := Ty.productMany (arguments.map (fun x => x.type)) }
          (some parameter) with
      | error error =>
          simp [argumentResult, bind, Except.bind] at success
      | ok fittedArgument =>
          simp only [argumentResult, bind, Except.bind] at success
          cases resultResult : withExpected context fittedArgument.state
              { id := call, type := returnType } expected with
          | error error =>
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := fittedArgument.coercions
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              exact Unchanged.trans
                (withExpected_direct_eq argumentResult)
                (withExpected_direct_eq resultResult)
  | none =>
      simp only [partsResult] at success
      generalize freshResultEq : state.fresh = freshResult at success
      rcases freshResult with ⟨resultType, freshState⟩
      cases unifyResult : unify freshState calleeType
          (.function (Ty.productMany (arguments.map fun x => x.type))
            resultType) with
      | error error =>
          simp [unifyResult, bind, Except.bind] at success
      | ok unifiedState =>
          simp only [unifyResult, bind, Except.bind] at success
          cases resultResult : withExpected context unifiedState
              { id := call, type := resultType } expected with
          | error error =>
              simp [resultResult] at success
          | ok fittedResult =>
              simp only [resultResult] at success
              change Except.ok {
                result := fittedResult.expression
                argumentCoercions := []
                callCoercions := fittedResult.coercions
                state := fittedResult.state
              } = Except.ok result at success
              injection success with resultEq
              subst result
              have freshSubset :
                  Unchanged state freshState := by
                have subset := fresh_direct_unchanged state
                rw [freshResultEq] at subset
                exact subset
              exact Unchanged.trans freshSubset
                (Unchanged.trans (unify_direct_unchanged unifyResult)
                  (withExpected_direct_eq resultResult))

theorem bindLambdaParameters_direct_unchanged
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    Unchanged state result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [bindLambdaParameters] at success
      injection success with resultEq
      subst result
      exact .refl _
  | cons parameter rest induction =>
      cases parameterValue : parameter.value with
      | error =>
          simp [bindLambdaParameters, parameterValue, bind, Except.bind]
            at success
      | inferred name =>
          simp only [bindLambdaParameters, parameterValue] at success
          simp only [bind, Except.bind] at success
          repeat' first | split at success
          all_goals try simp_all only [exceptPure_eq_ok]
          all_goals try simp_all
          all_goals
            subst result
            subst_vars
            have tailSubset := induction _ _ _ (by assumption)
            simpa [State.fresh, State.allocateBinder] using tailSubset
      | typed marker name sourceType =>
          simp only [bindLambdaParameters, parameterValue] at success
          cases typeResult : resolveSourceType context sourceType with
          | error error =>
              simp [typeResult, bind, Except.bind] at success
          | ok type =>
              simp only [typeResult, bind, Except.bind] at success
              repeat' first | split at success
              all_goals try simp_all only [exceptPure_eq_ok]
              all_goals try simp_all
              all_goals
                subst result
                subst_vars
                have tailSubset := induction _ _ _ (by assumption)
                simpa [State.allocateBinder] using tailSubset

theorem unifyBuiltinFunctionArgumentsEqual_direct_unchanged
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    Unchanged state next := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual] at success
      injection success with nextEq
      subst next
      exact .refl _
  | cons argument arguments induction =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          injection success with nextEq
          subst next
          exact .refl _
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at success
          cases unifyResult : unify state argument.type parameter with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok unified =>
              simp only [unifyResult, bind, Except.bind] at success
              exact Unchanged.trans
                (unify_direct_unchanged unifyResult)
                (induction success)


theorem recordBuiltinFunctionCall_direct_unchanged
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    Unchanged state result.2 := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have argumentsProgress := unifyBuiltinFunctionArgumentsEqual_direct_unchanged (by assumption)
  all_goals try have unifiedProgress := unify_direct_unchanged (by assumption)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress


private def PreservesDirectRequirements {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Unchanged initial (stateOf result)

private theorem inferMatchPatternFlatFuel_direct_unchanged_internal
    (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    PreservesDirectRequirements InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      PreservesDirectRequirements InferredPattern.state state
        (inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      PreservesDirectRequirements InferredPatterns.state state
        (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold PreservesDirectRequirements at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel, bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try have unifyProgress := unify_direct_unchanged (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.allocateBinder]
    all_goals first
      | exact .refl _
      | assumption
      | exact Unchanged.addRequirementWithId _ _
      | exact (Unchanged.addRequirementWithId _ _).trans unifyProgress
      | grind [Unchanged.trans, freshDataConstructorInstantiation_direct_unchanged,
          freshTypes_direct_unchanged]

theorem inferMatchPatternFuel_direct_unchanged
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    Unchanged state result.2 := by
  unfold inferMatchPatternFuel at success
  cases flatResult :
      inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error =>
      simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      injection success with resultEq
      subst result
      exact inferMatchPatternFlatFuel_direct_unchanged_internal fuel context pattern
        expected [] state inferred flatResult



end Solcore.Frontend.SourceInference.DirectCallEvents
