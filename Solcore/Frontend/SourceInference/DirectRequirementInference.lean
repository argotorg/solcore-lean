import Solcore.Frontend.SourceInference.DirectRequirementProgress

/-! Direct-call classification follows actual successful inference steps. -/
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.Detail
open TypeSystem
open State (DirectRequirementsProgress)

private theorem pureState_eq {state next : State}
    (accepted : (pure state : Except Error State) = .ok next) : state = next :=
  Except.ok.inj accepted

@[simp] private theorem exceptPure_eq_ok {epsilon alpha : Type}
    (value result : alpha) : ((pure value : Except epsilon alpha) = .ok result) ↔ value = result :=
  by change (Except.ok value = Except.ok result) ↔ value = result; simp

theorem unify_direct_progress {state next : State} {left right : Ty}
    (accepted : unify state left right = .ok next) : DirectRequirementsProgress state next := by
  unfold unify at accepted
  cases unified : state.inference.unify left right <;>
    simp [liftUnification, unified, bind, Except.bind] at accepted
  cases accepted
  exact .refl _

theorem freshTypes_direct_progress (count : Nat) (state : State) :
    DirectRequirementsProgress state (freshTypes count state).2 := by
  induction count generalizing state with
  | zero => exact .refl _
  | succ count ih => exact ih state.fresh.2

theorem freshDataConstructorInstantiation_direct_progress
    (dataType : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) (state : State) :
    DirectRequirementsProgress state (freshDataConstructorInstantiation dataType constructor state).2 := by
  let step : List Ty × State → TypeParameterId → List Ty × State :=
    fun result _ => (result.1 ++ [result.2.fresh.1], result.2.fresh.2)
  have foldProgress (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      DirectRequirementsProgress accumulator.2 (parameters.foldl step accumulator).2 := by
    induction parameters generalizing accumulator with
    | nil => exact .refl _
    | cons parameter parameters ih => exact ih (step accumulator parameter)
  exact foldProgress dataType.parameters ([], state)

theorem attachExpressionCoercions_direct_progress (state : State) (entries : List ExpressionCoercions) :
    DirectRequirementsProgress state (attachExpressionCoercions state entries) := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => exact .refl _
  | cons entry rest ih =>
    simp only [List.foldl_cons]
    exact ih (state.modifyExpressionNode entry.expression fun node => appendExpressionCoercions node entry.coercions)

theorem recordExpression_direct_progress
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (state : State)
    (localSchemeInstantiationStart : Option Nat := none) :
    DirectRequirementsProgress state
      (recordExpression source expression form requirements coercions state localSchemeInstantiationStart).2 :=
  .refl _

theorem recordExpressionWithExpected_direct_progress
    {context : Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State} {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) : DirectRequirementsProgress state result.2 :=
  .of_direct_eq (recordExpressionWithExpected_requirements_subset accepted)
    (recordExpressionWithExpected_preserves_requirementsWellFormed accepted)
    (recordExpressionWithExpected_direct_eq accepted)

theorem recordSelectedCallResult_direct_progress
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult)
    (result : InferredExpression) (trailingCoercions : List CoercionStep) (state : State) :
    DirectRequirementsProgress state
      (recordSelectedCallResult source callee name arguments attempt result trailingCoercions state).2 :=
  attachExpressionCoercions_direct_progress state attempt.argumentCoercions

theorem recordSelectedCall_direct_progress
    (source callee : Syntax.Expr) (name : String)
    (arguments : List InferredExpression) (attempt : CandidateAttemptResult) :
    DirectRequirementsProgress attempt.state (recordSelectedCall source callee name arguments attempt).2 :=
  recordSelectedCallResult_direct_progress source callee name arguments attempt attempt.result [] attempt.state

theorem recordIndirectCall_direct_progress (source : Syntax.Expr) (callee : InferredExpression)
    (arguments : List InferredExpression) (result : IndirectApplicationResult) :
    DirectRequirementsProgress result.state (recordIndirectCall source callee arguments result).2 := .refl _

theorem selectFunctionCandidateFrom_direct_progress
    {context : Context} {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option Ty} {state : State} {result : CandidateAttemptResult}
    (accepted : selectFunctionCandidateFrom context name candidates arguments
      integerLiteralOrigins call expected state = .ok result) :
    DirectRequirementsProgress state result.state := by
  obtain ⟨signature, _, selected⟩ := selectFunctionCandidateFrom_success_candidate accepted
  exact tryFunctionCandidate_direct_progress selected

theorem inferUnaryOperator_direct_progress
    {context : Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    DirectRequirementsProgress state result.state := by
  unfold inferUnaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact DirectRequirementsProgress.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _)
    | exact (unify_direct_progress (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_progress (state := state) (by assumption)).trans
        (unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _))

theorem inferBinaryOperator_direct_progress
    {context : Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (success : inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    DirectRequirementsProgress state result.state := by
  unfold inferBinaryOperator at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact .refl _
    | exact unifiedProgress
    | exact DirectRequirementsProgress.addRequirementsWithIds _ _
    | exact unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _)
    | exact (unify_direct_progress (state := state) (by assumption)).trans unifiedProgress
    | exact (unify_direct_progress (state := state) (by assumption)).trans
        (unifiedProgress.trans (DirectRequirementsProgress.addRequirementsWithIds _ _))


private theorem fresh_direct_progress (state : State) :
    DirectRequirementsProgress state state.fresh.2 := .refl _

theorem applyFunctionType_direct_progress
    {context : Context} {call : ExpressionId} {calleeType : Ty}
    {arguments : List InferredExpression} {expected : Option Ty}
    {state : State} {result : IndirectApplicationResult}
    (success : applyFunctionType context call calleeType arguments expected
      state = .ok result) :
    DirectRequirementsProgress state result.state := by
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
              exact DirectRequirementsProgress.trans
                (withExpected_direct_progress argumentResult)
                (withExpected_direct_progress resultResult)
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
                  DirectRequirementsProgress state freshState := by
                have subset := fresh_direct_progress state
                rw [freshResultEq] at subset
                exact subset
              exact DirectRequirementsProgress.trans freshSubset
                (DirectRequirementsProgress.trans (unify_direct_progress unifyResult)
                  (withExpected_direct_progress resultResult))

theorem bindLambdaParameters_direct_progress
    {context : Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {state : State}
    {result : List TypedBinder × List Ty × State}
    (success : bindLambdaParameters context parameters index seen state =
      .ok result) :
    DirectRequirementsProgress state result.2.2 := by
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

theorem unifyBuiltinFunctionArgumentsEqual_direct_progress
    {arguments : List InferredExpression} {parameters : List Ty}
    {state next : State}
    (success : unifyBuiltinFunctionArgumentsEqual arguments parameters state =
      .ok next) :
    DirectRequirementsProgress state next := by
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
              exact DirectRequirementsProgress.trans
                (unify_direct_progress unifyResult)
                (induction success)


theorem recordBuiltinFunctionCall_direct_progress
    {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {call : ExpressionId} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : recordBuiltinFunctionCall source callee name function arguments
      call expected state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  unfold recordBuiltinFunctionCall at success
  simp_all [bind, Except.bind]
  repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all
  all_goals try
    have pureEq := pureState_eq (by assumption)
    subst_vars
  all_goals try have argumentsProgress := unifyBuiltinFunctionArgumentsEqual_direct_progress (by assumption)
  all_goals try have unifiedProgress := unify_direct_progress (by assumption)
  all_goals first
    | exact argumentsProgress
    | exact argumentsProgress.trans unifiedProgress


private theorem progress_compose
    {r1 r2 r3 : List Requirement} {n1 n2 n3 : Nat} {d1 d2 d3 : List RequirementId}
    (left : RequirementLedgerProgress r1 n1 d1 r2 n2 d2)
    (right : RequirementLedgerProgress r2 n2 d2 r3 n3 d3) :
    RequirementLedgerProgress r1 n1 d1 r3 n3 d3 := by
  refine ⟨left.included.trans right.included,
    fun wf => right.wellFormed (left.wellFormed wf),
    fun wf allocated => right.allocated (left.wellFormed wf) (left.allocated wf allocated), ?_⟩
  intro wf id member
  have secondMember : id ∈ r2.map Requirement.id := by
    obtain ⟨requirement, present, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨requirement, left.included present, same⟩
  exact (right.existing (left.wellFormed wf) id secondMember).trans (left.existing wf id member)

private def PreservesDirectRequirements {alpha : Type} (stateOf : alpha → State)
    (initial : State) (computation : Except Error alpha) : Prop :=
  ∀ result, computation = .ok result → DirectRequirementsProgress initial (stateOf result)

private theorem inferMatchPatternFlatFuel_direct_progress_internal
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
    all_goals try have unifyProgress := unify_direct_progress (by assumption)
    all_goals try specialize ih1 _ _ _ heq
    all_goals try specialize ih1 _ _ heq
    all_goals try specialize ih2 _ heq
    all_goals try simp_all [State.fresh, State.allocateBinder]
    all_goals first
      | exact .refl _
      | assumption
      | exact DirectRequirementsProgress.addRequirementWithId _ _
      | exact (DirectRequirementsProgress.addRequirementWithId _ _).trans unifyProgress
      | grind [progress_compose, freshDataConstructorInstantiation_direct_progress,
          freshTypes_direct_progress]

theorem inferMatchPatternFuel_direct_progress
    {fuel : Nat} {context : Context} {pattern : Syntax.Pattern}
    {expected : Ty} {state : State} {result : TypedMatchPattern × State}
    (success : inferMatchPatternFuel fuel context pattern expected state =
      .ok result) :
    DirectRequirementsProgress state result.2 := by
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
      exact inferMatchPatternFlatFuel_direct_progress_internal fuel context pattern
        expected [] state inferred flatResult


private theorem pair_success_direct_progress {alpha : Type}
    {operation : alpha × State} {value : alpha} {next initial : State}
    (operationSubset : DirectRequirementsProgress initial operation.2)
    (success : operation = (value, next)) :
    DirectRequirementsProgress initial next := by
  simpa [success] using operationSubset

private theorem pair_eq_property {alpha beta : Type} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state, result = (value, state) → property state) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state rfl

private theorem pair_except_property {epsilon alpha beta : Type}
    {computation : Except epsilon (alpha × beta)} {result : alpha × beta}
    {property : beta → Prop}
    (invariant : ∀ value state,
      computation = .ok (value, state) → property state)
    (success : computation = .ok result) :
    property result.2 := by
  rcases result with ⟨value, state⟩
  exact invariant value state success

private theorem anchored_pair_except_property {epsilon alpha beta : Type}
    {anchor : alpha × State}
    {computation : alpha → State → Except epsilon (beta × State)}
    {initial state : State} {result : beta × State}
    (_anchorInvariant : ∀ value next,
      (Except.ok anchor : Except epsilon (alpha × State)) =
          Except.ok (value, next) →
        DirectRequirementsProgress initial next)
    (invariant : ∀ value state result next,
      computation value state = .ok (result, next) →
        DirectRequirementsProgress state next)
    (success : computation anchor.1 state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  rcases anchor with ⟨value, anchorState⟩
  rcases result with ⟨result, next⟩
  exact invariant value state result next success


private theorem allocateExpressionId_success_direct_progress
    {state next : State} {id : ExpressionId}
    (success : state.allocateExpressionId = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem allocateStatementId_success_direct_progress
    {state next : State} {id : StatementId}
    (success : state.allocateStatementId = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem state_fresh_success_direct_progress
    {state next : State} {type : Ty}
    (success : state.fresh = (type, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress (DirectRequirementsProgress.refl state)
    success

private theorem allocateHiddenLocal_success_direct_progress
    {state next : State} {id : Resolved.LocalId}
    (success : state.allocateHiddenLocal = (id, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem addRequirementWithId_success_direct_progress
    {state next : State} {predicate : ProgramPredicate}
    {requirement : RequirementId}
    (success : state.addRequirementWithId predicate = (requirement, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.addRequirementWithId state predicate) success

private theorem addRequirementsWithIds_success_direct_progress
    {state next : State} {predicates : List ProgramPredicate}
    {requirements : List RequirementId}
    (success : state.addRequirementsWithIds predicates = (requirements, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.addRequirementsWithIds state predicates) success

private theorem allocateBinder_success_direct_progress
    {state next : State} {name : String} {scheme : Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement} {binder : TypedBinder}
    (success : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (DirectRequirementsProgress.refl state) success

private theorem freshDataConstructorInstantiation_success_direct_progress
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : State} {instantiation : DataConstructorInstantiation}
    (success : freshDataConstructorInstantiation dataType constructor state =
      (instantiation, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (freshDataConstructorInstantiation_direct_progress dataType constructor
      state) success

private theorem freshTypes_success_direct_progress
    {count : Nat} {state next : State} {types : List Ty}
    (success : freshTypes count state = (types, next)) :
    DirectRequirementsProgress state next :=
  pair_success_direct_progress
    (freshTypes_direct_progress count state) success

private theorem syntheticTuple_result_direct_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : (pure ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) : Except Error (InferredExpression × State)) = .ok result) :
    DirectRequirementsProgress state result.snd := by
  have resultEq : ({
      id := state.allocateExpressionId.fst
      type := Ty.productMany (elements.map (·.type))
    }, state.allocateExpressionId.snd.recordNode (.expression {
      id := state.allocateExpressionId.fst
      span
      type := Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact DirectRequirementsProgress.trans
    (DirectRequirementsProgress.refl state)
    (DirectRequirementsProgress.refl state)

private theorem syntheticTuple_pair_direct_progress
    {elements : List InferredExpression} {span : Syntax.SourceSpan}
    {state : State} {result : InferredExpression × State}
    (success : ({
        id := state.allocateExpressionId.fst
        type := Ty.productMany (elements.map (·.type))
      }, state.allocateExpressionId.snd.recordNode (.expression {
        id := state.allocateExpressionId.fst
        span
        type := Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = result) :
    DirectRequirementsProgress state result.snd := by
  rw [← success]
  exact DirectRequirementsProgress.trans
    (DirectRequirementsProgress.refl state)
    (DirectRequirementsProgress.refl state)

private theorem pure_pair_result_direct_progress {epsilon alpha : Type}
    {value : alpha} {next initial : State} {result : alpha × State}
    (nextSubset : DirectRequirementsProgress initial next)
    (success : (pure (value, next) : Except epsilon (alpha × State)) =
      .ok result) :
    DirectRequirementsProgress initial result.snd := by
  have resultEq : (value, next) = result := by
    simpa only [exceptPure_eq_ok] using success
  rw [← resultEq]
  exact nextSubset

private theorem restored_pair_result_direct_progress {alpha : Type}
    {value : alpha} {state initial : State} {scope : LexicalScope}
    {result : alpha × State}
    (subset : DirectRequirementsProgress initial state)
    (success : (value, state.restoreLexicalScope scope) = result) :
    DirectRequirementsProgress initial result.snd := by
  rw [← success]
  exact DirectRequirementsProgress.trans subset
    (DirectRequirementsProgress.refl state)


set_option maxHeartbeats 2000000 in
private theorem inferFuel_direct_progress_internal :
    (∀ fuel context expression expected state,
      PreservesDirectRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state)) ∧
    (∀ fuel context source id instantiation arguments expected state,
      PreservesDirectRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state)) ∧
    (∀ fuel context sources expected state,
      PreservesDirectRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state)) ∧
    (∀ fuel context statements expectedReturn state,
      PreservesDirectRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state)) ∧
    (∀ fuel context statement expectedReturn state,
      PreservesDirectRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state)) ∧
    (∀ fuel context items state,
      PreservesDirectRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state)) ∧
    (∀ fuel context item state,
      PreservesDirectRequirements Prod.snd state
        (inferForItemFuel fuel context item state)) ∧
    (∀ fuel context target state,
      PreservesDirectRequirements Prod.snd state
        (inferPlaceFuel fuel context target state)) ∧
    (∀ fuel context target operator value state,
      PreservesDirectRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state)) ∧
    (∀ fuel context expressions state,
      PreservesDirectRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state)) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      PreservesDirectRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state)) := by
  apply inferExprFuel.mutual_induct
    (motive1 := fun fuel context expression expected state =>
      PreservesDirectRequirements Prod.snd state
        (inferExprFuel fuel context expression expected state))
    (motive2 := fun fuel context source id instantiation arguments expected
        state =>
      PreservesDirectRequirements Prod.snd state
        (inferConstructorApplicationFuel fuel context source id instantiation
          arguments expected state))
    (motive3 := fun fuel context sources expected state =>
      PreservesDirectRequirements Prod.snd state
        (inferConstructorArgumentsFuel fuel context sources expected state))
    (motive4 := fun fuel context statements expectedReturn state =>
      PreservesDirectRequirements BlockResult.state state
        (inferStatementsFuel fuel context statements expectedReturn state))
    (motive5 := fun fuel context statement expectedReturn state =>
      PreservesDirectRequirements StatementResult.state state
        (inferStatementFuel fuel context statement expectedReturn state))
    (motive6 := fun fuel context items state =>
      PreservesDirectRequirements InferredForItems.state state
        (inferForItemsFuel fuel context items state))
    (motive7 := fun fuel context item state =>
      PreservesDirectRequirements Prod.snd state
        (inferForItemFuel fuel context item state))
    (motive8 := fun fuel context target state =>
      PreservesDirectRequirements Prod.snd state
        (inferPlaceFuel fuel context target state))
    (motive9 := fun fuel context target operator value state =>
      PreservesDirectRequirements (fun result => result.2.2) state
        (inferAssignedValueFuel fuel context target operator value state))
    (motive10 := fun fuel context expressions state =>
      PreservesDirectRequirements Prod.snd state
        (inferExprsFuel fuel context expressions state))
    (motive11 := fun fuel context scrutineeType expectedReturn outerScope
        cases state =>
      PreservesDirectRequirements MatchCasesResult.state state
        (inferMatchCasesFuel fuel context scrutineeType expectedReturn outerScope
          cases state))
  case case44 =>
    intros context statement expectedReturn state fuel id stateAfterId
      statementIdEq scrutinees arms statementEq sources notSingleton
      casesInduction bodyInduction expressionsInduction
    unfold PreservesDirectRequirements at *
    intro result success
    have statementIdSubset :=
      allocateStatementId_success_direct_progress statementIdEq
    unfold inferStatementFuel at success
    simp only [statementIdEq, statementEq, bind, Except.bind] at success
    repeat' first | split at success
    all_goals try cases success
    all_goals try exact (notSingleton _ (by assumption)).elim
    all_goals try have expressionsSubset :=
      expressionsInduction _ (by assumption)
    all_goals try have casesSubset :=
      casesInduction _ _ _ (by assumption)
    all_goals try have bodySubset :=
      bodyInduction _ _ _ (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_result_direct_progress (by assumption)
    all_goals try have tupleSubset :=
      syntheticTuple_pair_direct_progress (by assumption)
    all_goals try have defaultSubset :=
      pure_pair_result_direct_progress casesSubset (by assumption)
    all_goals simp_all only [exceptPure_eq_ok]
    all_goals try have restoredSubset :=
      restored_pair_result_direct_progress bodySubset (by assumption)
    all_goals try simp_all
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind [progress_compose]
  case case70 =>
    intros fuel context target operator value state placeInduction valueInduction
    unfold PreservesDirectRequirements at *
    intro result success
    unfold inferAssignedValueFuel at success
    simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨place, placeState⟩
    all_goals try rcases v_2 with ⟨inferred, resultState⟩
    all_goals
      have placeSubset := pair_except_property placeInduction rfl
    all_goals try have valueSubset :=
      valueInduction place v_1 inferred resultState (by assumption)
    all_goals try
      have valueSubset := anchored_pair_except_property placeInduction
        valueInduction (by assumption)
    all_goals try have valueSubset :=
      pair_except_property (valueInduction _ _) (by assumption)
    all_goals try have unifiedSubset :=
      unify_direct_progress (by assumption)
    all_goals simp_all
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind [progress_compose]
  case case67 =>
    unfold PreservesDirectRequirements at *
    intros
    simp_all only [inferPlaceFuel]
  all_goals
    intros
    unfold PreservesDirectRequirements at *
    intro result success
    first
      | unfold inferExprFuel at success
      | unfold inferConstructorApplicationFuel at success
      | unfold inferConstructorArgumentsFuel at success
      | unfold inferStatementsFuel at success
      | unfold inferStatementFuel at success
      | unfold inferForItemsFuel at success
      | unfold inferForItemFuel at success
      | unfold inferPlaceFuel at success
      | unfold inferAssignedValueFuel at success
      | unfold inferExprsFuel at success
      | unfold inferMatchCasesFuel at success
    try simp_all [bind, Except.bind]
    repeat' first | split at success
    all_goals try cases success
    all_goals try simp_all only [exceptPure_eq_ok]
    all_goals try rcases v with ⟨v0a, v0b⟩
    all_goals try rcases v_1 with ⟨v1a, v1b⟩
    all_goals try rcases v_2 with ⟨v2a, v2b⟩
    all_goals try rcases v_3 with ⟨v3a, v3b⟩
    all_goals try rcases v_4 with ⟨v4a, v4b⟩
    all_goals try subst_vars
    all_goals first
      | specialize ih1 _ _ (by assumption)
      | specialize ih1 _ _ _ (by assumption)
      | specialize ih1 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih2 _ _ (by assumption)
      | specialize ih2 _ _ _ (by assumption)
      | specialize ih2 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | specialize ih3 _ _ (by assumption)
      | specialize ih3 _ _ _ (by assumption)
      | specialize ih3 _ _ _ _ (by assumption)
      | skip
    all_goals first
      | have ih1Subset := pair_eq_property ih1
      | have ih1Subset := pair_except_property ih1 (by assumption)
      | have ih1Subset := pair_except_property (ih1 _ _) (by assumption)
      | skip
    all_goals first
      | have ih2Subset := pair_eq_property ih2
      | have ih2Subset := pair_except_property ih2 (by assumption)
      | have ih2Subset := pair_except_property (ih2 _ _) (by assumption)
      | skip
    all_goals first
      | have ih3Subset := pair_eq_property ih3
      | have ih3Subset := pair_except_property ih3 (by assumption)
      | have ih3Subset := pair_except_property (ih3 _ _) (by assumption)
      | skip
    all_goals try have unifiedSubset :=
      unify_direct_progress (by assumption)
    all_goals try have expressionIdSubset :=
      allocateExpressionId_success_direct_progress (by assumption)
    all_goals try have statementIdSubset :=
      allocateStatementId_success_direct_progress (by assumption)
    all_goals try have freshSubset :=
      state_fresh_success_direct_progress (by assumption)
    all_goals try have hiddenLocalSubset :=
      allocateHiddenLocal_success_direct_progress (by assumption)
    all_goals try have requirementSubset :=
      addRequirementWithId_success_direct_progress (by assumption)
    all_goals try have requirementsSubset :=
      addRequirementsWithIds_success_direct_progress (by assumption)
    all_goals try have binderSubset :=
      allocateBinder_success_direct_progress (by assumption)
    all_goals try have constructorSubset :=
      freshDataConstructorInstantiation_success_direct_progress (by
        assumption)
    all_goals try have typesSubset :=
      freshTypes_success_direct_progress (by assumption)
    all_goals try have recordSubset :=
      recordExpressionWithExpected_direct_progress (by assumption)
    all_goals try have issuedRecord :=
      (DirectRequirementsProgress.addRequirementWithId _ _).trans recordSubset
    all_goals try have batchRecord :=
      (DirectRequirementsProgress.addRequirementsWithIds _ _).trans recordSubset
    all_goals try have lambdaSubset :=
      bindLambdaParameters_direct_progress (by assumption)
    all_goals try
      have afterLambdaSubset := DirectRequirementsProgress.trans lambdaSubset
        (unify_direct_progress (by assumption))
    all_goals try have patternSubset :=
      inferMatchPatternFuel_direct_progress (by assumption)
    all_goals try have unarySubset :=
      inferUnaryOperator_direct_progress (by assumption)
    all_goals try have binarySubset :=
      inferBinaryOperator_direct_progress (by assumption)
    all_goals try have selectionSubset :=
      selectFunctionCandidateFrom_direct_progress (by assumption)
    all_goals try have expectedSubset :=
      withExpected_direct_progress (by assumption)
    all_goals try have applicationSubset :=
      applyFunctionType_direct_progress (by assumption)
    all_goals try have builtinSubset :=
      recordBuiltinFunctionCall_direct_progress (by assumption)
    all_goals try simp_all
    all_goals try exact DirectRequirementsProgress.addRequirementWithId _ _
    all_goals try exact DirectRequirementsProgress.refl _
    all_goals dsimp only [State.DirectRequirementsProgress,
      State.recordNode, State.allocateExpressionId, State.allocateStatementId,
      State.allocateHiddenLocal, State.allocateBinder, State.restoreLexicalScope,
      State.withLocals, State.fresh, recordExpression, recordIndirectCall] at *
    all_goals grind
      [progress_compose,
        State.DirectRequirementsProgress.addRequirementWithId,
        State.DirectRequirementsProgress.addRequirementsWithIds,
        freshDataConstructorInstantiation_direct_progress,
        freshTypes_direct_progress,
        recordExpression_direct_progress,
        recordSelectedCallResult_direct_progress,
        recordSelectedCall_direct_progress,
        recordIndirectCall_direct_progress]

theorem inferExprFuel_direct_progress
    {fuel : Nat} {context : Context} {expression : Syntax.Expr}
    {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferExprFuel fuel context expression expected state =
      .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.1 fuel context expression
    expected state result success

theorem inferConstructorApplicationFuel_direct_progress
    {fuel : Nat} {context : Context} {source : Syntax.Expr}
    {id : ExpressionId} {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (success : inferConstructorApplicationFuel fuel context source id
      instantiation arguments expected state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.1 fuel context source id
    instantiation arguments expected state result success

theorem inferConstructorArgumentsFuel_direct_progress
    {fuel : Nat} {context : Context} {sources : List Syntax.Expr}
    {expected : List Ty} {state : State}
    {result : List InferredExpression × State}
    (success : inferConstructorArgumentsFuel fuel context sources expected
      state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.1 fuel context sources
    expected state result success

theorem inferStatementsFuel_direct_progress
    {fuel : Nat} {context : Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : BlockResult}
    (success : inferStatementsFuel fuel context statements expectedReturn state =
      .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.1 fuel context
    statements expectedReturn state result success

theorem inferStatementFuel_direct_progress
    {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {expectedReturn : Ty} {state : State} {result : StatementResult}
    (success : inferStatementFuel fuel context statement expectedReturn state =
      .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.1 fuel context
    statement expectedReturn state result success

theorem inferForItemsFuel_direct_progress
    {fuel : Nat} {context : Context} {items : List Syntax.ForItem}
    {state : State} {result : InferredForItems}
    (success : inferForItemsFuel fuel context items state = .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.1 fuel context
    items state result success

theorem inferForItemFuel_direct_progress
    {fuel : Nat} {context : Context} {item : Syntax.ForItem}
    {state : State} {result : ForItemForm × State}
    (success : inferForItemFuel fuel context item state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.1 fuel context
    item state result success

theorem inferPlaceFuel_direct_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {state : State} {result : PlaceResolution × State}
    (success : inferPlaceFuel fuel context target state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.1 fuel
    context target state result success

theorem inferAssignedValueFuel_direct_progress
    {fuel : Nat} {context : Context} {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp} {value : Syntax.Expr} {state : State}
    {result : AssignmentResolution × InferredExpression × State}
    (success : inferAssignedValueFuel fuel context target operator value state =
      .ok result) :
    DirectRequirementsProgress state result.2.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.1 fuel
    context target operator value state result success

theorem inferExprsFuel_direct_progress
    {fuel : Nat} {context : Context} {expressions : List Syntax.Expr}
    {state : State} {result : List InferredExpression × State}
    (success : inferExprsFuel fuel context expressions state = .ok result) :
    DirectRequirementsProgress state result.2 := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.2.1 fuel
    context expressions state result success

theorem inferMatchCasesFuel_direct_progress
    {fuel : Nat} {context : Context} {scrutineeType expectedReturn : Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : State} {result : MatchCasesResult}
    (success : inferMatchCasesFuel fuel context scrutineeType expectedReturn
      outerScope cases state = .ok result) :
    DirectRequirementsProgress state result.state := by
  exact inferFuel_direct_progress_internal.2.2.2.2.2.2.2.2.2.2 fuel
    context scrutineeType expectedReturn outerScope cases state result success

end Solcore.Frontend.SourceInference.Detail
