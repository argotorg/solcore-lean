import Solcore.Frontend.SourceInference.Internal.LocalReadOrigins

/-!
# Direct call origins

Each direct-call requirement has an actual declaration-call emitter, and classified templates are a
subset of those calls. These are the progress invariants.
-/

section
-- leanmerge: from Solcore.Frontend.SourceInference.ClassifiedCallHelpers
/-! Actual inference helpers preserve the classified-template inventory.
Only binder allocation adds entries, handled separately in the traversal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.ClassifiedCallEvents
open TypeSystem Detail

abbrev Unchanged (before after : State) : Prop :=
  after.localSchemeAssumptions = before.localSchemeAssumptions
namespace Unchanged
theorem refl (state : State) : Unchanged state state := rfl
theorem trans {before middle after : State}
    (first : Unchanged before middle) (second : Unchanged middle after) :
    Unchanged before after := Eq.trans second first
theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Unchanged state (state.addRequirementWithId predicate).2 := rfl
theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Unchanged state (state.addRequirementsWithIds predicates).2 :=
  by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest ih => exact ih (state.addRequirementWithId predicate).2
end Unchanged
private theorem pureState_eq {state next : State}
    (accepted : (pure state : Except Error State) = .ok next) : state = next :=
  Except.ok.inj accepted

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type}
    (value result : alpha) : ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp

theorem unify_classified_unchanged {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Unchanged state next := by
  unfold unify at accepted
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at accepted
  cases accepted
  exact .refl _

theorem freshTypes_classified_unchanged (count : Nat) (state : State) :
    Unchanged state (freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact ih state.fresh.2

theorem freshDataConstructorInstantiation_classified_unchanged
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

theorem attachExpressionCoercions_classified_unchanged (state : State) (entries : List ExpressionCoercions) :
    Unchanged state (attachExpressionCoercions state entries) := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    exact ih (state.modifyExpressionNode entry.expression fun node => appendExpressionCoercions node entry.coercions)

theorem recordExpression_classified_unchanged
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    Unchanged state
      (recordExpression source expression form requirements coercions state localSchemeInstantiationStart).2 :=
  .refl _

theorem commitCoercionPlan_classified_eq (state : State)
    (plan : List PlannedCoercionStep) :
    (commitCoercionPlan state plan).2.localSchemeAssumptions =
      state.localSchemeAssumptions := by
  induction plan generalizing state with
  | nil => rfl
  | cons step rest ih =>
    change (commitCoercionPlan
      ((state.addRequirementWithId step.predicate).2.addRequirementsWithIds
        step.methodPredicates).2 rest).2.localSchemeAssumptions = _
    rw [ih, Unchanged.addRequirementsWithIds]
    rfl

/-- Coercion requirements remain operational; expected-type fitting never
marks either old or newly issued rows as declaration-call templates. -/
theorem withExpected_classified_eq
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : withExpected context state actual expected = .ok result) :
    result.state.localSchemeAssumptions = state.localSchemeAssumptions := by
  unfold withExpected at accepted
  split at accepted
  · cases accepted
    rfl
  · split at accepted
    · cases accepted
      rfl
    · split at accepted
      all_goals try contradiction
      all_goals
        simp only [bind, Except.bind] at accepted
        split at accepted
        · contradiction
        · split at accepted
          · contradiction
          · cases accepted
            exact commitCoercionPlan_classified_eq _ _

theorem recordExpressionWithExpected_classified_eq
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result) :
    result.2.localSchemeAssumptions = state.localSchemeAssumptions := by
  obtain ⟨fitted, accepted, _, same⟩ :=
    recordExpressionWithExpected_success_record accepted
  rw [same]
  exact withExpected_classified_eq accepted

theorem recordExpressionWithExpected_classified_unchanged
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State} {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) : Unchanged state result.2 :=
  recordExpressionWithExpected_classified_eq accepted

theorem recordSelectedCallResult_classified_unchanged
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    Unchanged state
      (recordSelectedCallResult source callee name arguments attempt result trailingCoercions state).2 :=
  attachExpressionCoercions_classified_unchanged state attempt.argumentCoercions

theorem recordSelectedCall_classified_unchanged
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Unchanged attempt.state (recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_classified_unchanged source callee name arguments attempt attempt.result [] attempt.state

theorem recordIndirectCall_classified_unchanged (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Unchanged result.state (recordIndirectCall source callee arguments result).2 := .refl _

theorem inferUnaryOperator_classified_unchanged
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
  all_goals try have unifiedProgress := unify_classified_unchanged (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact Unchanged.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _)
    | exact (unify_classified_unchanged (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_classified_unchanged (state := state) (by assumption)).trans
        (unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _))

theorem inferBinaryOperator_classified_unchanged
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Unchanged state result.state := by
  unfold inferBinaryOperator binaryOperatorTail at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_classified_unchanged (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact Unchanged.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _)
    | exact (unify_classified_unchanged (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_classified_unchanged (state := state) (by assumption)).trans
        (unifiedProgress.trans (Unchanged.addRequirementsWithIds _ _))


private theorem fresh_classified_unchanged (state : State) :
    Unchanged state state.fresh.2 := .refl _

theorem applyFunctionType_classified_unchanged
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
                (withExpected_classified_eq argumentResult)
                (withExpected_classified_eq resultResult)
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
                have subset := fresh_classified_unchanged state
                rw [freshResultEq] at subset
                exact subset
              exact Unchanged.trans freshSubset
                (Unchanged.trans (unify_classified_unchanged unifyResult)
                  (withExpected_classified_eq resultResult))

theorem bindLambdaParameters_classified_unchanged
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

theorem unifyBuiltinFunctionArgumentsEqual_classified_unchanged
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
                (unify_classified_unchanged unifyResult)
                (induction success)


theorem recordBuiltinFunctionCall_classified_unchanged
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
  all_goals try have argumentsProgress := unifyBuiltinFunctionArgumentsEqual_classified_unchanged (by assumption)
  all_goals try have unifiedProgress := unify_classified_unchanged (by assumption)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress


private def PreservesDirectRequirements {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Unchanged initial (stateOf result)

private theorem inferMatchPatternFlatFuel_classified_unchanged_internal
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
    all_goals try have unifyProgress := unify_classified_unchanged (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.allocateBinder]
    all_goals first
      | exact .refl _
      | assumption
      | exact Unchanged.addRequirementWithId _ _
      | exact (Unchanged.addRequirementWithId _ _).trans unifyProgress
      | grind [Unchanged.trans, freshDataConstructorInstantiation_classified_unchanged,
          freshTypes_classified_unchanged]

theorem inferMatchPatternFuel_classified_unchanged
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
      exact inferMatchPatternFlatFuel_classified_unchanged_internal fuel context pattern
        expected [] state inferred flatResult



theorem candidateWithExpected_classified_unchanged
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : candidateWithExpected context state actual expected = .ok (some result)) :
    Unchanged state result.state := by
  unfold candidateWithExpected at accepted
  cases fitted : withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    subst result
    exact withExpected_classified_eq fitted
  | error error =>
    cases error <;> simp_all
    rename_i error
    cases error <;> simp_all

theorem fitArguments_classified_unchanged
    {context : Context} {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : ArgumentFitResult}
    (accepted : fitArguments context state arguments parameters = .ok (some result)) :
    Unchanged state result.state := by
  induction arguments generalizing state parameters result with
  | nil =>
    cases parameters <;> simp_all [fitArguments]
    subst result
    exact .refl _
  | cons argument arguments ih =>
    cases parameters with
    | nil => simp [fitArguments] at accepted
    | cons parameter parameters =>
      unfold fitArguments at accepted
      cases fitted : candidateWithExpected context state argument (some parameter) with
      | error error => simp [fitted, bind, Except.bind] at accepted
      | ok value =>
        cases value with
        | none => simp [fitted, bind, Except.bind] at accepted
        | some fit =>
          simp only [fitted, bind, Except.bind] at accepted
          cases remaining : fitArguments context fit.state arguments parameters with
          | error error => simp [remaining] at accepted
          | ok value =>
            cases value with
            | none => simp [remaining] at accepted
            | some tail =>
              simp only [remaining, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at accepted
              subst result
              exact (candidateWithExpected_classified_unchanged fitted).trans (ih (result := tail) remaining)

/-- The sole inference operation that marks direct-call rows allocates its
signature predicates after argument/result fitting, then marks exactly them. -/
theorem tryFunctionCandidate_classified_unchanged
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State}
    {signature : ProgramFunctionSignature} {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    Unchanged state result.state := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals have argumentsProgress := fitArguments_classified_unchanged (by assumption)
  all_goals have resultProgress := candidateWithExpected_classified_unchanged (by assumption)
  all_goals
    exact (Unchanged.refl state).trans
      (argumentsProgress.trans (resultProgress.trans
        (Unchanged.addRequirementsWithIds _ _)))


theorem selectFunctionCandidateFrom_classified_unchanged
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) : Unchanged state result.state := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_classified_unchanged selected

end Solcore.Frontend.SourceInference.ClassifiedCallEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallClassificationHelpers
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
  unfold inferBinaryOperator binaryOperatorTail at success
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
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallOriginsProgress
/-! Each direct-call requirement has an actual declaration-call emitter in
the source node table. Candidate selection temporarily holds its fresh batch;
recording the selected call discharges that batch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.DirectCallEvents
open TypeSystem Detail

/-- The actual call node records the exact issued requirement identity. -/
def HasCall (nodes : List Node) (requirement : RequirementId) : Prop :=
  ∃ node, .expression node ∈ nodes ∧
    ∃ callee arguments instantiation,
      node.form = .call callee arguments (.declaration instantiation) ∧
      requirement ∈ node.requirements

def OriginsFields (nodes : List Node) (direct : List RequirementId) : Prop :=
  ∀ requirement ∈ direct, HasCall nodes requirement

abbrev Origins (state : State) : Prop :=
  OriginsFields state.nodes state.directCallRequirements

def ProgressFields (beforeNodes : List Node) (beforeDirect : List RequirementId)
    (afterNodes : List Node) (afterDirect : List RequirementId) : Prop :=
  OriginsFields beforeNodes beforeDirect → OriginsFields afterNodes afterDirect

abbrev Progress (before after : State) : Prop :=
  ProgressFields before.nodes before.directCallRequirements
    after.nodes after.directCallRequirements

theorem HasCall.mono {before after : List Node} {requirement : RequirementId}
    (call : HasCall before requirement) (included : before ⊆ after) :
    HasCall after requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued⟩ := call
  exact ⟨node, included member, callee, arguments, instantiation, form, issued⟩

theorem HasCall.modifyStatementNode {state : State} {requirement : RequirementId}
    (call : HasCall state.nodes requirement)
    (id : StatementId) (modify : StatementNode → StatementNode) :
    HasCall (state.modifyStatementNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued⟩ := call
  exact ⟨node, List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation, form, issued⟩

theorem HasCall.modifyExpressionNode {state : State} {requirement : RequirementId}
    (call : HasCall state.nodes requirement)
    (id : ExpressionId) (modify : ExpressionNode → ExpressionNode)
    (form : ∀ node, (modify node).form = node.form)
    (requirements : ∀ node, node.requirements ⊆ (modify node).requirements) :
    HasCall (state.modifyExpressionNode id modify).nodes requirement := by
  obtain ⟨node, member, callee, arguments, instantiation, original, issued⟩ := call
  by_cases selected : node.id = id
  · refine ⟨{ modify node with id }, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, (form node).trans original, requirements node issued⟩
    simp [selected]
  · refine ⟨node, List.mem_map.mpr ⟨.expression node, member, ?_⟩,
      callee, arguments, instantiation, original, issued⟩
    simp [selected]

theorem HasCall.attachExpressionCoercions {state : State} {requirement : RequirementId}
    (call : HasCall state.nodes requirement) (entries : List ExpressionCoercions) :
    HasCall (attachExpressionCoercions state entries).nodes requirement := by
  unfold Detail.attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact call
  | cons entry rest ih =>
    apply ih
    exact call.modifyExpressionNode entry.expression
      (fun node => appendExpressionCoercions node entry.coercions)
      (fun _ => rfl) (fun _ => List.subset_append_left _ _)

theorem ProgressFields.trans {bn mn an : List Node} {bd md ad : List RequirementId}
    (first : ProgressFields bn bd mn md) (second : ProgressFields mn md an ad) :
    ProgressFields bn bd an ad := fun origins => second (first origins)

theorem ProgressFields.statement (nodes : List Node) (direct : List RequirementId)
    (statement : StatementNode) :
    ProgressFields nodes direct (nodes ++ [.statement statement]) direct :=
  fun origins requirement member => (origins requirement member).mono (List.subset_append_left _ _)

theorem ProgressFields.expression (nodes : List Node) (direct : List RequirementId)
    (expression : ExpressionNode) :
    ProgressFields nodes direct (nodes ++ [.expression expression]) direct :=
  fun origins requirement member => (origins requirement member).mono (List.subset_append_left _ _)

namespace Progress

theorem refl (state : State) : Progress state state := fun origins => origins

theorem trans {before middle after : State}
    (first : Progress before middle) (second : Progress middle after) : Progress before after :=
  ProgressFields.trans first second

theorem of_nodes_eq {before after : State} (nodes : after.nodes = before.nodes)
    (direct : Unchanged before after) : Progress before after := by
  intro origins
  simpa only [OriginsFields, nodes, direct] using origins

theorem recordStatement (state : State) (node : StatementNode) :
    Progress state (state.recordNode (.statement node)) :=
  ProgressFields.statement _ _ _

theorem modifyStatementNode (state : State) (id : StatementId)
    (modify : StatementNode → StatementNode) :
    Progress state (state.modifyStatementNode id modify) :=
  fun origins requirement member => (origins requirement member).modifyStatementNode id modify

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 := of_nodes_eq rfl rfl

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_nodes_eq (State.addRequirementsWithIds_nodes _ _) (State.addRequirementsWithIds_direct_eq _ _)

theorem recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (state : State) (start : Option Nat := none) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 :=
  ProgressFields.expression _ _ _

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Progress state result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  exact (of_nodes_eq (withExpected_occurrenceState_eq fit).1
    (withExpected_direct_eq fit)).trans (ProgressFields.expression _ _ _)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress state next :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1 (unify_direct_unchanged accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  of_nodes_eq (withExpected_occurrenceState_eq accepted).1 (withExpected_direct_eq accepted)

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_nodes_eq (inferUnaryOperator_occurrenceState_eq accepted).1 (inferUnaryOperator_direct_unchanged accepted)

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_nodes_eq (inferBinaryOperator_occurrenceState_eq accepted).1 (inferBinaryOperator_direct_unchanged accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_nodes_eq (applyFunctionType_occurrenceState_eq accepted).1 (applyFunctionType_direct_unchanged accepted)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 :=
  of_nodes_eq (bindLambdaParameters_occurrenceState_eq accepted).1 (bindLambdaParameters_direct_unchanged accepted)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_nodes_eq (Detail.freshDataConstructorInstantiation_nodes _ _ _)
    (freshDataConstructorInstantiation_direct_unchanged _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_nodes_eq (Detail.freshTypes_nodes _ _) (freshTypes_direct_unchanged _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  have direct := recordSelectedCallResult_direct_unchanged source callee name arguments attempt result trailing state
  rw [direct] at member
  apply ((origins requirement member).attachExpressionCoercions attempt.argumentCoercions).mono
  intro node present
  exact List.mem_append_left _ (List.mem_append_left _ present)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  ProgressFields.expression _ _ _

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  intro origins requirement member
  have direct := recordBuiltinFunctionCall_direct_unchanged accepted
  rw [direct] at member
  obtain ⟨calleeId, nodes⟩ := Detail.recordBuiltinFunctionCall_success_nodes accepted
  exact (origins requirement member).mono (by rw [nodes]; exact List.subset_append_left _ _)

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  of_nodes_eq (inferMatchPatternFuel_occurrenceState_eq accepted).1 (inferMatchPatternFuel_direct_unchanged accepted)

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  apply Progress.trans (middle := allocated)
  · rw [allocatedEq]; exact refl _
  · have recording := recordExpressionWithExpected recorded
    refine ProgressFields.trans ?_ recording
    simp only [State.addRequirementsWithIds_nodes, State.addRequirementsWithIds_direct_eq]
    exact refl _

end Progress
end Solcore.Frontend.SourceInference.DirectCallEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.DirectCallCandidateOrigins
/-! Selected candidate batches are exactly the signature identities recorded
on their real declaration-call node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.Frontend.SourceInference.DirectCallEvents
open TypeSystem Detail

private theorem candidateWithExpected_direct_unchanged
    {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : candidateWithExpected context state actual expected = .ok (some result)) :
    Unchanged state result.state := by
  unfold candidateWithExpected at accepted
  cases fitted : withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    subst result
    exact withExpected_direct_eq fitted
  | error error =>
    cases error <;> simp_all
    rename_i error
    cases error <;> simp_all

private theorem fitArguments_direct_unchanged
    {context : Context} {state : State} {arguments : List InferredExpression}
    {parameters : List Ty} {result : ArgumentFitResult}
    (accepted : fitArguments context state arguments parameters = .ok (some result)) :
    Unchanged state result.state := by
  induction arguments generalizing state parameters result with
  | nil =>
    cases parameters <;> simp_all [fitArguments]
    subst result
    rfl
  | cons argument arguments ih =>
    cases parameters with
    | nil => simp [fitArguments] at accepted
    | cons parameter parameters =>
      unfold fitArguments at accepted
      cases fitted : candidateWithExpected context state argument (some parameter) with
      | error error => simp [fitted, bind, Except.bind] at accepted
      | ok value =>
        cases value with
        | none => simp [fitted, bind, Except.bind] at accepted
        | some fit =>
          simp only [fitted, bind, Except.bind] at accepted
          cases remaining : fitArguments context fit.state arguments parameters with
          | error error => simp [remaining] at accepted
          | ok value =>
            cases value with
            | none => simp [remaining] at accepted
            | some tail =>
              simp only [remaining, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at accepted
              subst result
              exact Unchanged.trans (candidateWithExpected_direct_unchanged fitted)
                (ih (result := tail) remaining)

theorem tryFunctionCandidate_direct_batch
    {context : Context} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId}
    {expected : Option Ty} {state : State} {signature : ProgramFunctionSignature}
    {result : CandidateAttemptResult}
    (accepted : tryFunctionCandidate context arguments integerLiteralOrigins
      call expected state signature = .ok (some result)) :
    result.state.directCallRequirements = state.directCallRequirements ++ result.signatureRequirements := by
  unfold tryFunctionCandidate at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals have argumentsSame := fitArguments_direct_unchanged (by assumption)
  all_goals have resultSame := candidateWithExpected_direct_unchanged (by assumption)
  all_goals
    change _ ++ _ = _
    rw [State.addRequirementsWithIds_direct_eq, resultSame, argumentsSame]

theorem selectFunctionCandidateFrom_direct_batch
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    result.state.directCallRequirements = state.directCallRequirements ++ result.signatureRequirements := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_direct_batch selected

/-- Recording the selected call discharges exactly its pending signature batch. -/
theorem recordSelectedCallResult_pending
    {before state : State} {attempt : CandidateAttemptResult}
    (nodes : state.nodes = before.nodes)
    (direct : state.directCallRequirements = before.directCallRequirements ++ attempt.signatureRequirements)
    (source callee : Syntax.Expr) (name : String) (arguments : List InferredExpression)
    (result : InferredExpression) (trailing : List CoercionStep) :
    Progress before (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  intro origins requirement member
  rw [recordSelectedCallResult_direct_unchanged, direct] at member
  rcases List.mem_append.mp member with prior | fresh
  · have original : HasCall state.nodes requirement := by
      rw [nodes]
      exact origins requirement prior
    apply (original.attachExpressionCoercions attempt.argumentCoercions).mono
    intro node present
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · let calleeId := (Detail.attachExpressionCoercions state attempt.argumentCoercions).allocateExpressionId.1
    let callNode : ExpressionNode := {
      id := result.id, span := source.span, type := result.type
      form := .call calleeId (arguments.map (·.id)) (.declaration attempt.instantiation)
      requirements := coercionRequirements attempt.callCoercions ++ attempt.signatureRequirements ++
        coercionRequirements trailing
      coercions := attempt.callCoercions ++ trailing }
    refine ⟨callNode, ?_, calleeId, arguments.map (·.id), attempt.instantiation, rfl, ?_⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (List.mem_append_right _ fresh)

namespace Progress

theorem selectAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {attempt : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok attempt)
    (source callee : Syntax.Expr) :
    Progress state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_pending (selectFunctionCandidateFrom_occurrenceState_eq accepted).1
    (selectFunctionCandidateFrom_direct_batch accepted) source callee name arguments _ _

theorem selectFitAndRecord
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected selectedExpected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {fitted : ExpectationResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call selectedExpected state = .ok attempt)
    (fit : Detail.withExpected context attempt.state attempt.result expected = .ok fitted)
    (source callee : Syntax.Expr) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt
      fitted.expression fitted.coercions fitted.state).2 :=
  recordSelectedCallResult_pending
    ((withExpected_occurrenceState_eq fit).1.trans (selectFunctionCandidateFrom_occurrenceState_eq accepted).1)
    ((withExpected_direct_eq fit).trans (selectFunctionCandidateFrom_direct_batch accepted))
    source callee name arguments _ _

end Progress
end Solcore.Frontend.SourceInference.DirectCallEvents
end

section
-- leanmerge: from Solcore.Frontend.SourceInference.ClassifiedCallProgress
/-! Classified templates are a subset of actual declaration-call IDs. The
relation follows only these two inventories, so unrelated state changes are
transparent. Generalized allocation is the sole operation adding templates. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.ClassifiedCallEvents
open TypeSystem Detail

def Classified (state : State) : Prop :=
  state.localSchemeAssumptions ⊆ state.directCallRequirements

def ProgressFields (beforeTemplates beforeDirect afterTemplates afterDirect : List RequirementId) : Prop :=
  (beforeTemplates ⊆ beforeDirect) → (afterTemplates ⊆ afterDirect)
abbrev Progress (before after : State) : Prop :=
  ProgressFields before.localSchemeAssumptions before.directCallRequirements
    after.localSchemeAssumptions after.directCallRequirements

theorem ProgressFields.trans {bt bd mt md ats ad : List RequirementId}
    (first : ProgressFields bt bd mt md) (second : ProgressFields mt md ats ad) :
    ProgressFields bt bd ats ad := fun prior => second (first prior)

theorem ProgressFields.refl (templates direct : List RequirementId) :
    ProgressFields templates direct templates direct := id

namespace Progress

theorem refl (state : State) : Progress state state := id

theorem trans {before middle after : State} (first : Progress before middle) (second : Progress middle after) :
    Progress before after := fun prior => second (first prior)

theorem of_eq {before after : State}
    (templates : after.localSchemeAssumptions = before.localSchemeAssumptions)
    (direct : after.directCallRequirements = before.directCallRequirements) : Progress before after := by
  intro classified
  change after.localSchemeAssumptions ⊆ after.directCallRequirements
  rwa [templates, direct]

theorem of_direct_extension {before after : State}
    (templates : after.localSchemeAssumptions = before.localSchemeAssumptions)
    (direct : before.directCallRequirements ⊆ after.directCallRequirements) : Progress before after := by
  intro classified requirement member
  exact direct (classified (templates ▸ member))

theorem recordStatement (state : State) (node : StatementNode) :
    Progress state (state.recordNode (.statement node)) := refl _
theorem modifyStatementNode (state : State) (id : StatementId) (modify : StatementNode → StatementNode) :
    Progress state (state.modifyStatementNode id modify) := refl _

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 := refl _
theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 :=
  of_eq (Unchanged.addRequirementsWithIds _ _) (State.addRequirementsWithIds_direct_eq _ _)

end Progress

namespace Progress
theorem recordExpression (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (state : State) (start : Option Nat := none) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 :=
  of_eq (recordExpression_classified_unchanged _ _ _ _ _ _ _) (DirectCallEvents.recordExpression_direct_unchanged _ _ _ _ _ _ _)

theorem recordExpressionWithExpected
    {context : Context} {source : Syntax.Expr} {id : ExpressionId} {type : Ty}
    {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result) :
    Progress state result.2 :=
  of_eq (recordExpressionWithExpected_classified_unchanged accepted) (DirectCallEvents.recordExpressionWithExpected_direct_unchanged accepted)

theorem unify {state next : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok next) : Progress state next :=
  of_eq (unify_classified_unchanged accepted) (DirectCallEvents.unify_direct_unchanged accepted)

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    Progress state result.state :=
  of_eq (withExpected_classified_eq accepted) (withExpected_direct_eq accepted)

theorem inferUnaryOperator
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_eq (inferUnaryOperator_classified_unchanged accepted) (DirectCallEvents.inferUnaryOperator_direct_unchanged accepted)

theorem inferBinaryOperator
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_eq (inferBinaryOperator_classified_unchanged accepted) (DirectCallEvents.inferBinaryOperator_direct_unchanged accepted)

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_eq (applyFunctionType_classified_unchanged accepted) (DirectCallEvents.applyFunctionType_direct_unchanged accepted)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 :=
  of_eq (bindLambdaParameters_classified_unchanged accepted) (DirectCallEvents.bindLambdaParameters_direct_unchanged accepted)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 :=
  of_eq (freshDataConstructorInstantiation_classified_unchanged _ _ _) (DirectCallEvents.freshDataConstructorInstantiation_direct_unchanged _ _ _)

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 :=
  of_eq (freshTypes_classified_unchanged _ _) (DirectCallEvents.freshTypes_direct_unchanged _ _)

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 :=
  of_eq (recordSelectedCallResult_classified_unchanged _ _ _ _ _ _ _ _) (DirectCallEvents.recordSelectedCallResult_direct_unchanged _ _ _ _ _ _ _ _)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  of_eq (recordSelectedCall_classified_unchanged _ _ _ _ _) (DirectCallEvents.recordSelectedCall_direct_unchanged _ _ _ _ _)

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  of_eq (recordIndirectCall_classified_unchanged _ _ _ _) (DirectCallEvents.recordIndirectCall_direct_unchanged _ _ _ _)

theorem recordBuiltinFunctionCall
    {source callee : Syntax.Expr} {name : String} {function : BuiltinFunctionId}
    {arguments : List InferredExpression} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 :=
  of_eq (recordBuiltinFunctionCall_classified_unchanged accepted) (DirectCallEvents.recordBuiltinFunctionCall_direct_unchanged accepted)

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 :=
  of_eq (inferMatchPatternFuel_classified_unchanged accepted) (DirectCallEvents.inferMatchPatternFuel_direct_unchanged accepted)

theorem selectFunctionCandidateFrom
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) : Progress state result.state := by
  apply of_direct_extension (selectFunctionCandidateFrom_classified_unchanged accepted)
  rw [DirectCallEvents.selectFunctionCandidateFrom_direct_batch accepted]
  exact List.subset_append_left _ _

theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  apply Progress.trans (middle := allocated)
  · rw [allocatedEq]; exact refl _
  · have recording := recordExpressionWithExpected recorded
    refine ProgressFields.trans ?_ recording
    simp only [Unchanged.addRequirementsWithIds, State.addRequirementsWithIds_direct_eq]
    exact refl _

end Progress
private theorem requirement_contains {ids : List RequirementId} {id : RequirementId}
    (member : ids.contains id = true) : id ∈ ids := by
  induction ids with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.contains_cons, Bool.or_eq_true] at member
    rcases member with same | later
    · apply List.mem_cons.mpr
      apply Or.inl
      have indices : id.index = head.index := by
        change (id.index == head.index) = true at same
        exact beq_iff_eq.mp same
      cases id; cases head; cases indices; rfl
    · exact List.mem_cons_of_mem _ (ih later)

/-- The generalizer selects templates only from genuine direct-call IDs. -/
theorem generalized_template_direct (state : State) (locals : TypeSystem.Environment)
    (cutoff : Nat) (type : Ty) (template : LocalSchemeRequirement)
    (member : template ∈ (Detail.generalizeValue state locals cutoff type).requirements) :
    template.templateRequirement ∈ state.directCallRequirements := by
  unfold Detail.generalizeValue at member
  dsimp only at member
  obtain ⟨raw, eligible, selected⟩ := List.mem_filterMap.mp member
  have classified := (List.mem_filter.mp eligible).2
  simp only [Bool.and_eq_true] at classified
  have direct := classified.1
  split at selected
  · cases selected
    exact requirement_contains direct
  · contradiction


/-- Adding exactly the templates selected by the real generalizer preserves
classification as declaration-call requirements. -/
theorem Progress.allocateGeneralized (state : State) (locals : Environment)
    (cutoff : Nat) (type : Ty) (name : String) (span : Option Syntax.SourceSpan) (comptime : Bool) :
    Progress state ((state.withLocals locals).allocateBinder name
      (generalizeValue state locals cutoff type).scheme span comptime
      (generalizeValue state locals cutoff type).requirements).2 := by
  intro classified requirement member
  rcases List.mem_append.mp member with old | added
  · exact classified old
  · obtain ⟨template, selected, same⟩ := List.mem_map.mp added
    subst requirement
    exact generalized_template_direct state locals cutoff type template selected

theorem ProgressFields.generalized (state : State) (locals : Environment) (cutoff : Nat) (type : Ty) :
    ProgressFields state.localSchemeAssumptions state.directCallRequirements
      (state.localSchemeAssumptions ++ (generalizeValue state locals cutoff type).requirements.map
        (fun requirement => requirement.templateRequirement)) state.directCallRequirements := by
  intro classified requirement member
  rcases List.mem_append.mp member with old | added
  · exact classified old
  · obtain ⟨template, selected, same⟩ := List.mem_map.mp added
    subst requirement
    exact generalized_template_direct state locals cutoff type template selected

theorem Progress.allocateEmpty (state : State) (name : String) (scheme : Scheme)
    (span : Option Syntax.SourceSpan) (comptime : Bool) :
    Progress state (state.allocateBinder name scheme span comptime []).2 := by
  intro classified
  simpa [State.allocateBinder] using classified

end Solcore.Frontend.SourceInference.ClassifiedCallEvents
end
