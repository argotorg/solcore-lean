import Solcore.Frontend.SourceInference.LocalReadScopeProgress

/-! Helper computations preserve exact local-reference identities. Actual local
identifier inference adds only the binder selected by its real lexical lookup. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalReadScopeProgress
open TypeSystem Detail

namespace Progress

theorem unify {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : Progress state next :=
  of_unchanged (Nat.le_of_eq (localReadScope_unify_preserves_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (unify_occurrenceState_eq accepted).1

theorem withExpected {context : Context} {state : State} {actual : InferredExpression}
    {expected : Option Ty} {result : ExpectationResult}
    (accepted : Detail.withExpected context state actual expected = .ok result) : Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_withExpected_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope accepted))
    (withExpected_occurrenceState_eq accepted).1

theorem selectFunctionCandidateFrom {context : Context} {name : String}
    {candidates : List ProgramFunctionSignature} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin} {call : ExpressionId} {expected : Option Ty}
    {state : State} {result : CandidateAttemptResult}
    (accepted : Detail.selectFunctionCandidateFrom context name candidates arguments integerLiteralOrigins
      call expected state = .ok result) : Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_selectFunctionCandidateFrom_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_selectFunctionCandidateFrom_lexicalScope accepted))
    (selectFunctionCandidateFrom_occurrenceState_eq accepted).1

theorem inferUnaryOperator {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_inferUnaryOperator_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (inferUnaryOperator_occurrenceState_eq accepted).1

theorem inferBinaryOperator {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_inferBinaryOperator_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (inferBinaryOperator_occurrenceState_eq accepted).1

theorem applyFunctionType {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (accepted : Detail.applyFunctionType context call calleeType arguments expected state = .ok result) :
    Progress state result.state :=
  of_unchanged (Nat.le_of_eq (localReadScope_applyFunctionType_nextLocal accepted).symm)
    (congrArg LexicalScope.binders (localReadScope_applyFunctionType_lexicalScope accepted))
    (applyFunctionType_occurrenceState_eq accepted).1

theorem recordExpressionWithExpected {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId} {expected : Option Ty}
    {state : State} {start : Option Nat} {result : InferredExpression × State}
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected state start = .ok result)
    (nonlocal : LocalReadEvents.Nonlocal form) : Progress state result.2 := by
  obtain ⟨fitted, fit, _, recorded⟩ := Detail.recordExpressionWithExpected_success_record accepted
  rw [recorded]
  apply (withExpected fit).trans
  apply recordExpression
  intro name localId same
  exact False.elim (nonlocal name localId same)

theorem recordNonlocal (state : State) (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId) (coercions : List CoercionStep)
    (start : Option Nat) (nonlocal : LocalReadEvents.Nonlocal form) :
    Progress state (Detail.recordExpression source expression form requirements coercions state start).2 := by
  apply recordExpression
  intro name localId same
  exact False.elim (nonlocal name localId same)

/-- The only new local reference in this branch names the actual looked-up
entry. A retired local identity cannot be manufactured by a type match. -/
theorem localIdentifier {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {name : Syntax.Identifier} {binder : TypedBinder} {result : InferredExpression × State}
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (accepted : inferExprFuel (fuel + 1) context expression expected initial = .ok result) :
    Progress initial result.2 := by
  have scope := inferExprFuel_success_lexicalScope_eq accepted
  have binders := congrArg LexicalScope.binders scope
  change result.2.localBinders = initial.localBinders at binders
  refine ⟨inferExprFuel_nextLocal_le accepted, ?_, ?_⟩
  · intro localId _ absent
    simpa only [binders] using absent
  · intro localId _ absent occurrence ⟨node, member, sameId, readForm⟩
    have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
    obtain ⟨fitted, fit, _, nodes⟩ := Detail.recordExpressionWithExpected_success_nodes recorded
    rw [nodes] at member
    rcases List.mem_append.mp member with old | fresh
    · have sameNodes := (Detail.withExpected_occurrenceState_eq fit).1
      rw [sameNodes] at old
      rw [State.addRequirementsWithIds_nodes] at old
      have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      change .expression node ∈ allocated.nodes at old
      rw [allocatedEq] at old
      exact ⟨node, old, sameId, readForm⟩
    · cases List.mem_singleton.mp fresh
      obtain ⟨actualName, actualForm⟩ := readForm
      have sameBinder : binder.id = localId := by cases actualForm; rfl
      have present := (State.lookupBinder?_eq_some_facts found).1
      have allocatedEq : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      rw [allocatedEq] at present
      exact False.elim (absent binder present sameBinder)


theorem fresh (state : State) : Progress state state.fresh.2 := Fields.refl _ _ _

theorem freshTypes (count : Nat) (state : State) : Progress state (Detail.freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact (fresh state).trans (ih state.fresh.2)

theorem freshDataConstructorInstantiation (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    Progress state (Detail.freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      Progress accumulator.2 (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl _
    | cons parameter parameters ih => exact (fresh accumulator.2).trans (ih (step accumulator parameter))
  unfold Detail.freshDataConstructorInstantiation
  exact fold dataType.parameters ([], state)

theorem addRequirementWithId (state : State) (predicate : ProgramPredicate) :
    Progress state (state.addRequirementWithId predicate).2 := Fields.refl _ _ _

theorem addRequirementsWithIds (state : State) (predicates : List ProgramPredicate) :
    Progress state (state.addRequirementsWithIds predicates).2 := by
  induction predicates generalizing state with
  | nil => exact .refl _
  | cons predicate rest ih =>
      exact (addRequirementWithId state predicate).trans (ih (state.addRequirementWithId predicate).2)

theorem bindLambdaParameters {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State} {result : List TypedBinder × List Ty × State}
    (accepted : Detail.bindLambdaParameters context parameters index seen state = .ok result) :
    Progress state result.2.2 := by
  induction parameters generalizing index seen state result with
  | nil =>
      simp only [Detail.bindLambdaParameters, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons parameter rest ih =>
      cases form : parameter.value with
      | error => simp [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
      | inferred name =>
          simp only [Detail.bindLambdaParameters, form, bind, Except.bind] at accepted
          repeat' first | split at accepted
          all_goals try cases accepted
          all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
          all_goals try subst_vars
          all_goals have tail := ih (by assumption)
          all_goals exact (fresh state).trans ((allocateBinder _ _ _ _ _ _).trans tail)
      | typed marker name syntaxType =>
          simp only [Detail.bindLambdaParameters, form] at accepted
          cases resolved : resolveSourceType context syntaxType with
          | error error => simp [resolved, bind, Except.bind] at accepted
          | ok type =>
              simp only [resolved, bind, Except.bind] at accepted
              repeat' first | split at accepted
              all_goals try cases accepted
              all_goals try simp_all only [pure, Except.pure, Except.ok.injEq]
              all_goals try subst_vars
              all_goals have tail := ih (by assumption)
              all_goals exact (allocateBinder _ _ _ _ _ _).trans tail

theorem recordSelectedCallResult (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailing : List CoercionStep) (state : State) :
    Progress state (Detail.recordSelectedCallResult source callee name arguments attempt result trailing state).2 := by
  unfold Detail.recordSelectedCallResult
  apply (attachExpressionCoercions _ _).trans
  apply (recordNonlocal _ _ _ (.reference name (.declaration attempt.instantiation)) _ _ _
    (by intro _ _ impossible; cases impossible)).trans
  exact recordNonlocal _ _ _ (.call _ _ (.declaration attempt.instantiation)) _ _ _
    (by intro _ _ impossible; cases impossible)

theorem recordSelectedCall (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    Progress attempt.state (Detail.recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult _ _ _ _ _ _ _ _

theorem recordIndirectCall (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    Progress result.state (Detail.recordIndirectCall source callee arguments result).2 :=
  recordNonlocal _ _ _ _ _ _ _ (by intro _ _ impossible; cases impossible)


private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem exceptThrow_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by
  intro impossible
  cases impossible

private def Preserves {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → Progress initial (stateOf result)

private theorem patternFlat (fuel : Nat) (context : Context) (pattern : Syntax.Pattern)
    (expected : Ty) (seen : List String) (state : State) :
    Preserves InferredPattern.state state
      (inferMatchPatternFlatFuel fuel context pattern expected seen state) := by
  apply inferMatchPatternFlatFuel.induct context
    (motive1 := fun fuel pattern expected seen state =>
      Preserves InferredPattern.state state
        (inferMatchPatternFlatFuel fuel context pattern expected seen state))
    (motive2 := fun fuel patterns expected seen state =>
      Preserves InferredPatterns.state state
        (inferMatchPatternsFlatFuel fuel context patterns expected seen state))
  all_goals
    intros
    unfold Preserves at *
    intro result success
    simp_all [inferMatchPatternFlatFuel, inferMatchPatternsFlatFuel, bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
    all_goals try have unifyProgress := unify (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try exact allocateBinder _ _ _ _ _ _
    all_goals try exact Progress.refl _
    all_goals try assumption
    all_goals try exact addRequirementWithId _ _
    all_goals try exact (addRequirementWithId _ _).trans unifyProgress
    all_goals try simp_all only [Prod.mk.injEq]
    all_goals try subst_vars
    all_goals dsimp only [Progress, State.fresh, State.allocateBinder, State.addRequirementWithId] at *
    all_goals grind [Fields.trans, freshDataConstructorInstantiation, freshTypes]

theorem inferMatchPatternFuel {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : Detail.inferMatchPatternFuel fuel context pattern expected state = .ok result) :
    Progress state result.2 := by
  unfold Detail.inferMatchPatternFuel at success
  cases flatResult : inferMatchPatternFlatFuel fuel context pattern expected [] state with
  | error error => simp [flatResult, bind, Except.bind] at success
  | ok inferred =>
      simp only [flatResult, bind, Except.bind] at success
      change Except.ok ({
        source := inferred.source
        type := inferred.state.resolve expected
        resolution := inferred.resolution
        requirements := inferred.requirements
      }, inferred.state) = Except.ok result at success
      cases success
      exact patternFlat fuel context pattern expected [] state inferred flatResult


private theorem builtinArguments {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (accepted : unifyBuiltinFunctionArgumentsEqual arguments parameters state = .ok next) :
    Progress state next := by
  induction arguments generalizing parameters state next with
  | nil =>
      simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
      cases accepted
      exact .refl _
  | cons argument arguments ih =>
      cases parameters with
      | nil =>
          simp only [unifyBuiltinFunctionArgumentsEqual, Except.ok.injEq] at accepted
          cases accepted
          exact .refl _
      | cons parameter parameters =>
          simp only [unifyBuiltinFunctionArgumentsEqual] at accepted
          cases unified : Detail.unify state argument.type parameter with
          | error error => simp [unified, bind, Except.bind] at accepted
          | ok ready =>
              simp only [unified, bind, Except.bind] at accepted
              exact (unify unified).trans (ih accepted)

theorem recordBuiltinFunctionCall {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : Detail.recordBuiltinFunctionCall source callee name function arguments call expected state = .ok result) :
    Progress state result.2 := by
  unfold Detail.recordBuiltinFunctionCall at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
  all_goals try subst_vars
  all_goals have argumentsProgress := builtinArguments (by assumption)
  all_goals try have unifiedProgress := unify (by assumption)
  all_goals dsimp only [Progress, Detail.recordExpression, State.recordNode,
    State.allocateExpressionId] at *
  all_goals refine Fields.trans ?_ (Fields.expression _ _ _ _ ?_)
  all_goals try (intro _ _ impossible; cases impossible)
  all_goals refine Fields.trans ?_ (Fields.expression _ _ _ _ ?_)
  all_goals try (intro _ _ impossible; cases impossible)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress

end Progress
end Solcore.Frontend.SourceInference.LocalReadScopeProgress
