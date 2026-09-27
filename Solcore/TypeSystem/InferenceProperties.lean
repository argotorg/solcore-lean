import Solcore.TypeSystem.Inference

/-! Structural projection laws for reusable inference state operations. -/

set_option autoImplicit false

namespace Solcore.TypeSystem.InferState

/-- The inference allocator stays strictly above every variable mentioned by
its solved substitution. -/
def Solved (state : InferState) : Prop :=
  state.substitution.SolvedBelow state.next

@[simp] theorem fresh_substitution (state : InferState) :
    state.fresh.2.substitution = state.substitution := by
  rfl

@[simp] theorem fresh_next (state : InferState) :
    state.fresh.2.next = state.next + 1 := by
  rfl

/-- Scheme instantiation can only advance the state's allocator. -/
theorem instantiate_next_le (state : InferState) (scheme : Scheme) :
    state.next ≤ (state.instantiate scheme).2.next := by
  simpa [instantiate] using Scheme.instantiate_next_le scheme state.next

@[simp] theorem instantiate_substitution (state : InferState)
    (scheme : Scheme) :
    (state.instantiate scheme).2.substitution = state.substitution := by
  simp [instantiate]

@[simp] theorem instantiateDeclaration_substitution (state : InferState)
    (scheme : DeclarationScheme) :
    (state.instantiateDeclaration scheme).2.substitution =
      state.substitution := by
  simp [instantiateDeclaration]

/-- Declaration instantiation can only advance the state's allocator. -/
theorem instantiateDeclaration_next_le (state : InferState)
    (scheme : DeclarationScheme) :
    state.next ≤ (state.instantiateDeclaration scheme).2.next := by
  simpa [instantiateDeclaration] using
    DeclarationScheme.instantiate_next_le scheme state.next

theorem unify_next {state result : InferState} {left right : Ty}
    (success : state.unify left right = .ok result) :
    result.next = state.next := by
  unfold unify at success
  cases unified : Unification.unifyTypes (state.resolve left)
      (state.resolve right) <;>
    simp [unified, bind, Except.bind] at success
  cases success
  rfl

theorem solve_next {state result : InferState}
    {constraints : List Constraint}
    (success : state.solve constraints = .ok result) :
    result.next = state.next := by
  unfold solve at success
  cases unified : Unification.unify
      (constraints.map (Constraint.apply state.substitution)) <;>
    simp [unified, bind, Except.bind] at success
  cases success
  rfl

/-- Successful incremental binary unification makes the original input types
equal when resolved by the returned state. -/
theorem unify_resolve_eq
    {state result : InferState} {left right : Ty}
    (success : state.unify left right = .ok result) :
    result.resolve left = result.resolve right := by
  unfold InferState.unify at success
  cases unified : Unification.unifyTypes (state.resolve left)
      (state.resolve right) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      simpa [InferState.resolve, Substitution.compose_apply] using
        (Unification.unifyTypes_sound unified)

/-- Successful incremental constraint solving makes every original constraint
equal when resolved by the returned state. -/
theorem solve_satisfies
    {state result : InferState} {constraints : List Constraint}
    (success : state.solve constraints = .ok result) :
    ConstraintsSatisfiedBy result.substitution constraints := by
  unfold InferState.solve at success
  cases unified : Unification.unify
      (constraints.map (·.apply state.substitution)) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      have normalizedSatisfied :=
        Unification.unify_sound unified
      intro constraint member
      have appliedMember : constraint.apply state.substitution ∈
          constraints.map (·.apply state.substitution) :=
        List.mem_map.mpr ⟨constraint, member, rfl⟩
      have equality := normalizedSatisfied
        (constraint.apply state.substitution) appliedMember
      simpa [Constraint.SatisfiedBy, Constraint.apply,
        Substitution.compose_apply] using equality

namespace Solved

/-- Every initial inference state has a solved empty substitution. -/
theorem initial (next : Nat := 0) : (InferState.initial next).Solved := by
  exact Substitution.SolvedBelow.empty next

/-- Allocating one fresh variable preserves the solved-state invariant. -/
theorem fresh {state : InferState} (solved : state.Solved) :
    state.fresh.2.Solved := by
  exact solved.weaken (Nat.le_succ state.next)

/-- Rank-1 scheme instantiation preserves the solved-state invariant. -/
theorem instantiate {state : InferState} (solved : state.Solved)
    (scheme : Scheme) :
    (state.instantiate scheme).2.Solved := by
  exact solved.weaken (InferState.instantiate_next_le state scheme)

/-- Declaration scheme instantiation preserves the solved-state invariant. -/
theorem instantiateDeclaration {state : InferState} (solved : state.Solved)
    (scheme : DeclarationScheme) :
    (state.instantiateDeclaration scheme).2.Solved := by
  exact solved.weaken
    (InferState.instantiateDeclaration_next_le state scheme)

/-- Instantiating a bounded scheme in a solved state returns a type bounded by
the advanced state allocator. -/
theorem instantiate_type_variablesBelow
    {state : InferState} (solved : state.Solved) (scheme : Scheme)
    (freeBelow : scheme.FreeVariablesBelow state.next) :
    (state.instantiate scheme).1.VariablesBelow
      (state.instantiate scheme).2.next := by
  have rawBelow := Scheme.instantiate_variablesBelow scheme state.next freeBelow
  have stateSolved := solved.instantiate scheme
  have applied := stateSolved.variablesBelow_apply rawBelow
  simpa [InferState.instantiate, InferState.resolve] using applied

/-- Instantiating a bounded declaration scheme in a solved state returns a
type bounded by the advanced state allocator. -/
theorem instantiateDeclaration_type_variablesBelow
    {state : InferState} (solved : state.Solved)
    (scheme : DeclarationScheme)
    (bodyBelow : scheme.body.VariablesBelow state.next) :
    (state.instantiateDeclaration scheme).1.VariablesBelow
      (state.instantiateDeclaration scheme).2.next := by
  have rawBelow := DeclarationScheme.instantiate_variablesBelow
    scheme state.next bodyBelow
  have stateSolved := solved.instantiateDeclaration scheme
  have applied := stateSolved.variablesBelow_apply rawBelow
  simpa [InferState.instantiateDeclaration, InferState.resolve] using applied

/-- Successful binary unification preserves solved inference state when the
two types actually passed to the unifier lie below the allocator bound. -/
theorem unify
    {state result : InferState} {left right : Ty}
    (solved : state.Solved)
    (leftBelow : (state.resolve left).VariablesBelow state.next)
    (rightBelow : (state.resolve right).VariablesBelow state.next)
    (success : state.unify left right = .ok result) :
    result.Solved := by
  unfold InferState.unify at success
  cases unified : Unification.unifyTypes (state.resolve left)
      (state.resolve right) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      apply (Unification.unifyTypes_solvedBelow leftBelow rightBelow
        unified).compose solved
      apply Unification.unifyTypes_rangeAvoidsDomain
      · simpa [InferState.resolve] using
          solved.apply_variables_outside_domain left
      · simpa [InferState.resolve] using
          solved.apply_variables_outside_domain right
      · exact unified

/-- Successful constraint solving preserves solved inference state when the
normalized constraints actually passed to the unifier lie below the allocator
bound. -/
theorem solve
    {state result : InferState} {constraints : List Constraint}
    (solved : state.Solved)
    (normalizedBelow : ConstraintsBelow state.next
      (constraints.map (·.apply state.substitution)))
    (success : state.solve constraints = .ok result) :
    result.Solved := by
  have normalizedOutside : ConstraintsOutsideDomain state.substitution
      (constraints.map (·.apply state.substitution)) := by
    intro constraint member
    rcases List.mem_map.mp member with
      ⟨source, sourceMember, sourceEq⟩
    subst constraint
    exact
      ⟨solved.apply_variables_outside_domain source.left,
        solved.apply_variables_outside_domain source.right⟩
  unfold InferState.solve at success
  cases unified : Unification.unify
      (constraints.map (·.apply state.substitution)) with
  | error error =>
      simp [unified, bind, Except.bind] at success
  | ok update =>
      simp [unified, bind, Except.bind] at success
      cases success
      apply (Unification.unify_solvedBelow normalizedBelow unified).compose solved
      exact Unification.unify_rangeAvoidsDomain normalizedOutside unified

end Solved

end Solcore.TypeSystem.InferState

namespace Solcore.TypeSystem.Inference

private theorem inferFrom_preserves
    {environment : Environment} {expression : Expr}
    {state : InferState} {result : Result}
    (environmentBelow : environment.BodiesBelow state.next)
    (annotationsBelow : expression.AnnotationsBelow state.next)
    (stateSolved : state.Solved)
    (success : Detail.inferFrom environment expression state = .ok result) :
    state.next ≤ result.state.next ∧
      result.state.Solved ∧
      result.type.VariablesBelow result.state.next := by
  induction expression generalizing environment state result with
  | unit =>
      simp [Detail.inferFrom] at success
      cases success
      exact ⟨Nat.le_refl state.next, stateSolved, by simp [Ty.unit]⟩
  | bool value =>
      simp [Detail.inferFrom] at success
      cases success
      exact ⟨Nat.le_refl state.next, stateSolved, by simp [Ty.bool]⟩
  | word value =>
      simp [Detail.inferFrom] at success
      cases success
      exact ⟨Nat.le_refl state.next, stateSolved, by simp [Ty.word]⟩
  | «variable» name =>
      simp only [Detail.inferFrom] at success
      cases found : environment.lookup? name with
      | none => simp [found] at success
      | some scheme =>
          rw [found] at success
          simp only at success
          cases success
          have bodyBelow := environmentBelow (name, scheme)
            (Environment.lookup?_eq_some_mem found)
          exact
            ⟨InferState.instantiate_next_le state scheme,
              stateSolved.instantiate scheme,
              stateSolved.instantiate_type_variablesBelow scheme
                (Scheme.FreeVariablesBelow.of_body bodyBelow)⟩
  | pair left right leftInduction rightInduction =>
      simp only [Detail.inferFrom] at success
      cases leftCall : Detail.inferFrom environment left state with
      | error error =>
          simp [leftCall, bind, Except.bind] at success
      | ok leftResult =>
          rw [leftCall] at success
          simp only [bind, Except.bind] at success
          cases rightCall : Detail.inferFrom
              (environment.apply leftResult.state.substitution) right
              leftResult.state with
          | error error =>
              simp [rightCall] at success
          | ok rightResult =>
              rw [rightCall] at success
              simp only at success
              cases success
              have leftFacts := leftInduction environmentBelow
                annotationsBelow.1 stateSolved leftCall
              have environmentAtLeft := environmentBelow.weaken leftFacts.1
              have rightEnvironmentBelow :=
                environmentAtLeft.apply leftFacts.2.1
              have rightFacts := rightInduction rightEnvironmentBelow
                (annotationsBelow.2.weaken leftFacts.1) leftFacts.2.1
                rightCall
              have leftTypeAtRight := leftFacts.2.2.weaken rightFacts.1
              have resolvedLeft :=
                rightFacts.2.1.variablesBelow_apply leftTypeAtRight
              exact
                ⟨Nat.le_trans leftFacts.1 rightFacts.1,
                  rightFacts.2.1,
                  (Ty.variablesBelow_product_iff _ _ _).mpr
                    ⟨resolvedLeft, rightFacts.2.2⟩⟩
  | lambda parameter body induction =>
      simp only [Detail.inferFrom] at success
      cases bodyCall : Detail.inferFrom
          ((parameter, Scheme.mono state.fresh.1) :: environment) body
          state.fresh.2 with
      | error error =>
          simp [bodyCall, bind, Except.bind] at success
      | ok bodyResult =>
          rw [bodyCall] at success
          simp only [bind, Except.bind] at success
          cases success
          have freshLe : state.next ≤ state.fresh.2.next := by
            simp
          have freshSolved := stateSolved.fresh
          have parameterBelow :
              state.fresh.1.VariablesBelow state.fresh.2.next := by
            simp [InferState.fresh]
          have extendedEnvironmentBelow :
              Environment.BodiesBelow state.fresh.2.next
                ((parameter, Scheme.mono state.fresh.1) :: environment) :=
            Environment.BodiesBelow.cons parameterBelow
              (environmentBelow.weaken freshLe)
          have bodyFacts := induction extendedEnvironmentBelow
            (annotationsBelow.weaken freshLe) freshSolved bodyCall
          have parameterAtBody := parameterBelow.weaken bodyFacts.1
          have resolvedParameter :=
            bodyFacts.2.1.variablesBelow_apply parameterAtBody
          exact
            ⟨Nat.le_trans freshLe bodyFacts.1,
              bodyFacts.2.1,
              (Ty.variablesBelow_function_iff _ _ _).mpr
                ⟨resolvedParameter, bodyFacts.2.2⟩⟩
  | application function argument functionInduction argumentInduction =>
      simp only [Detail.inferFrom] at success
      cases functionCall : Detail.inferFrom environment function state with
      | error error =>
          simp [functionCall, bind, Except.bind] at success
      | ok functionResult =>
          rw [functionCall] at success
          simp only [bind, Except.bind] at success
          cases argumentCall : Detail.inferFrom
              (environment.apply functionResult.state.substitution) argument
              functionResult.state with
          | error error =>
              simp [argumentCall] at success
          | ok argumentResult =>
              rw [argumentCall] at success
              simp only at success
              cases unifyCall : argumentResult.state.fresh.2.unify
                  functionResult.type
                  (.function argumentResult.type
                    argumentResult.state.fresh.1) with
              | error error =>
                  simp [unifyCall] at success
              | ok finalState =>
                  simp [unifyCall] at success
                  cases success
                  have functionFacts := functionInduction environmentBelow
                    annotationsBelow.1 stateSolved functionCall
                  have environmentAtFunction :=
                    environmentBelow.weaken functionFacts.1
                  have argumentEnvironmentBelow :=
                    environmentAtFunction.apply functionFacts.2.1
                  have argumentFacts := argumentInduction
                    argumentEnvironmentBelow
                    (annotationsBelow.2.weaken functionFacts.1)
                    functionFacts.2.1 argumentCall
                  have freshLe : argumentResult.state.next ≤
                      argumentResult.state.fresh.2.next := by
                    simp
                  have freshSolved := argumentFacts.2.1.fresh
                  have resultTypeBelow :
                      argumentResult.state.fresh.1.VariablesBelow
                        argumentResult.state.fresh.2.next := by
                    simp [InferState.fresh]
                  have functionTypeAtFresh :=
                    (functionFacts.2.2.weaken argumentFacts.1).weaken freshLe
                  have resolvedFunctionBelow :=
                    freshSolved.variablesBelow_apply functionTypeAtFresh
                  have argumentTypeAtFresh :=
                    argumentFacts.2.2.weaken freshLe
                  have expectedFunctionBelow :
                      (Ty.function argumentResult.type
                        argumentResult.state.fresh.1).VariablesBelow
                          argumentResult.state.fresh.2.next :=
                    (Ty.variablesBelow_function_iff _ _ _).mpr
                      ⟨argumentTypeAtFresh, resultTypeBelow⟩
                  have resolvedExpectedBelow :=
                    freshSolved.variablesBelow_apply expectedFunctionBelow
                  have finalSolved := freshSolved.unify resolvedFunctionBelow
                    resolvedExpectedBelow unifyCall
                  have finalNext := InferState.unify_next unifyCall
                  have resultTypeAtFinal :
                      argumentResult.state.fresh.1.VariablesBelow
                        finalState.next := by
                    rw [finalNext]
                    exact resultTypeBelow
                  have resolvedResultBelow :=
                    finalSolved.variablesBelow_apply resultTypeAtFinal
                  exact
                    ⟨Nat.le_trans functionFacts.1 <|
                        Nat.le_trans argumentFacts.1 <|
                          Nat.le_trans freshLe (Nat.le_of_eq finalNext.symm),
                      finalSolved,
                      resolvedResultBelow⟩
  | letE name value body valueInduction bodyInduction =>
      simp only [Detail.inferFrom] at success
      cases valueCall : Detail.inferFrom environment value state with
      | error error =>
          simp [valueCall, bind, Except.bind] at success
      | ok valueResult =>
          rw [valueCall] at success
          simp only [bind, Except.bind] at success
          let appliedEnvironment :=
            environment.apply valueResult.state.substitution
          let valueType := valueResult.state.resolve valueResult.type
          let scheme := appliedEnvironment.generalize valueType
          cases bodyCall : Detail.inferFrom ((name, scheme) :: appliedEnvironment)
              body valueResult.state with
          | error error =>
              simp [appliedEnvironment, valueType, scheme, bodyCall] at success
          | ok bodyResult =>
              simp [appliedEnvironment, valueType, scheme, bodyCall] at success
              cases success
              have valueFacts := valueInduction environmentBelow
                annotationsBelow.1 stateSolved valueCall
              have environmentAtValue :=
                environmentBelow.weaken valueFacts.1
              have appliedEnvironmentBelow :
                  Environment.BodiesBelow valueResult.state.next
                    appliedEnvironment := by
                exact environmentAtValue.apply valueFacts.2.1
              have valueTypeBelow :
                  valueType.VariablesBelow valueResult.state.next := by
                exact valueFacts.2.1.variablesBelow_apply valueFacts.2.2
              have extendedEnvironmentBelow :
                  Environment.BodiesBelow valueResult.state.next
                    ((name, scheme) :: appliedEnvironment) := by
                exact Environment.BodiesBelow.cons valueTypeBelow
                  appliedEnvironmentBelow
              have bodyFacts := bodyInduction extendedEnvironmentBelow
                (annotationsBelow.2.weaken valueFacts.1) valueFacts.2.1
                bodyCall
              exact
                ⟨Nat.le_trans valueFacts.1 bodyFacts.1,
                  bodyFacts.2.1, bodyFacts.2.2⟩
  | annotation expression expected induction =>
      simp only [Detail.inferFrom] at success
      cases expressionCall : Detail.inferFrom environment expression state with
      | error error =>
          simp [expressionCall, bind, Except.bind] at success
      | ok expressionResult =>
          rw [expressionCall] at success
          simp only [bind, Except.bind] at success
          cases unifyCall : expressionResult.state.unify expressionResult.type
              expected with
          | error error =>
              simp [unifyCall] at success
          | ok finalState =>
              simp [unifyCall] at success
              cases success
              have expressionFacts := induction environmentBelow
                annotationsBelow.1 stateSolved expressionCall
              have expectedAtResult :=
                annotationsBelow.2.weaken expressionFacts.1
              have resolvedExpressionBelow :=
                expressionFacts.2.1.variablesBelow_apply expressionFacts.2.2
              have resolvedExpectedBelow :=
                expressionFacts.2.1.variablesBelow_apply expectedAtResult
              have finalSolved := expressionFacts.2.1.unify
                resolvedExpressionBelow resolvedExpectedBelow unifyCall
              have finalNext := InferState.unify_next unifyCall
              have expectedAtFinal : expected.VariablesBelow finalState.next := by
                rw [finalNext]
                exact expectedAtResult
              have resultBelow :=
                finalSolved.variablesBelow_apply expectedAtFinal
              exact
                ⟨Nat.le_trans expressionFacts.1
                    (Nat.le_of_eq finalNext.symm),
                  finalSolved, resultBelow⟩

/-- Successful inference from allocator-bounded annotations returns a solved
state and a result type bounded by that state's allocator. -/
theorem infer_solved_variablesBelow
    {environment : Environment} {expression : Expr} {result : Result}
    (annotationsBelow :
      expression.AnnotationsBelow environment.nextVariable)
    (success : infer environment expression = .ok result) :
    result.state.Solved ∧
      result.type.VariablesBelow result.state.next := by
  simp only [infer] at success
  cases workerCall : Detail.inferFrom environment expression
      (.initial environment.nextVariable) with
  | error error =>
      simp [workerCall, bind, Except.bind] at success
  | ok workerResult =>
      rw [workerCall] at success
      simp only [bind, Except.bind] at success
      cases success
      have facts := inferFrom_preserves
        (Environment.bodiesBelow_nextVariable environment)
        annotationsBelow (InferState.Solved.initial environment.nextVariable)
        workerCall
      exact
        ⟨facts.2.1,
          facts.2.1.variablesBelow_apply facts.2.2⟩

end Solcore.TypeSystem.Inference
