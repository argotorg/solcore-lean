import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyContracts

/-! The actual call branch preserves private scheme variables through
constructor dispatch, argument inference, overload selection, builtins and
indirect application. Recursive premises are exactly smaller-fuel cases. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

theorem freshDataConstructorInstantiation_requirements (dataType : ProgramDataSignature)
    (constructor : ProgramDataConstructorSignature) (state : State) :
    (freshDataConstructorInstantiation dataType constructor state).2.requirements = state.requirements := by
  have fold (parameters : List TypeParameterId) (accumulator : List Ty × State) :
      (parameters.foldl (fun result _ =>
        (result.1 ++ [result.2.fresh.1], result.2.fresh.2)) accumulator).2.requirements =
        accumulator.2.requirements := by
    induction parameters generalizing accumulator with
    | nil => rfl
    | cons parameter rest ih => exact ih (accumulator.1 ++ [accumulator.2.fresh.1], accumulator.2.fresh.2)
  exact fold dataType.parameters ([],state)

theorem inferExprFuel_call_private
    {protectedVars : List TypeVarId} {fuel : Nat} {context : SourceInference.Context}
    {expression callee : Syntax.Expr} {sourceArguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (expressionEq : expression.value = .call callee sourceArguments)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelPrivacy protectedVars fuel context expression
        initial.allocateExpressionId.1 instantiation sourceArguments.elements expected state)
    (argumentsInduction : InferExprsFuelPrivacy protectedVars fuel context
      sourceArguments.elements initial.allocateExpressionId.2)
    (calleeInduction : ∀ state, InferExprFuelPrivacy protectedVars fuel context callee none state) :
    InferExprFuelPrivacy protectedVars (fuel+1) context expression expected initial := by
  intro ready wellFormed bound live catalog validated canonical expectedBelow expectedSafe result success
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedPrivacy : SafeTransport protectedVars initial allocated := .of_substitution_eq rfl
  have allocatedLive : LiveBindersSafe protectedVars allocated := live.transport rfl allocatedPrivacy
  unfold inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated callee with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType, constructor⟩
        let freshResult := freshDataConstructorInstantiation dataType constructor allocated
        have candidateFacts := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have payloadClosed := validated.data_constructor_payloadTypes_variablesBelow candidateFacts.1 candidateFacts.2 0
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (fun type member => (payloadClosed type member).weaken (Nat.zero_le _))
        have freshPrivacy := fresh_constructor (dataType := dataType) allocatedReady bound payloadClosed
        have freshLive := allocatedLive.transport
          (congrArg LexicalScope.binders (freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor allocated)) freshPrivacy.1
        have freshWellFormed := (freshDataConstructorInstantiation_direct_progress dataType constructor allocated).wellFormed wellFormed
        have finished := constructorInduction freshResult.1 freshResult.2 freshProperties.2.1 freshWellFormed
          (fun v member => Nat.lt_of_lt_of_le (bound v member) freshProperties.1.next_le)
          freshLive catalog validated canonical freshProperties.2.2.2.1 freshPrivacy.2.1
          freshProperties.2.2.2.2 freshPrivacy.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          (fun type member => freshPrivacy.1 _ (expectedSafe type member)) result success
        refine ⟨allocatedPrivacy.trans (freshPrivacy.1.trans finished.1), finished.2.1, finished.2.2.1, ?_⟩
        intro row member fresh
        apply finished.2.2.2 row member
        change row ∉ allocated.requirements at fresh
        simpa only [freshResult, freshDataConstructorInstantiation_requirements] using fresh
    | nil =>
      simp only at success
      split at success
      · cases success
      · next _ missing _ =>
        cases missing with
        | some missing => rcases missing with ⟨qualifiers,name⟩; simp at success
        | none =>
          cases argumentsResult : inferExprsFuel fuel context sourceArguments.elements allocated with
          | error error => simp [argumentsResult] at success
          | ok argumentsPair =>
            rcases argumentsPair with ⟨arguments, argumentState⟩
            simp only [argumentsResult] at success
            have argumentsProperties := inferExprsFuel_inferenceProperties allocatedReady validated canonical argumentsResult
            have argumentsPrivacy := argumentsInduction allocatedReady wellFormed bound allocatedLive catalog validated canonical
              (arguments,argumentState) argumentsResult
            have prefixPrivacy := allocatedPrivacy.trans argumentsPrivacy.1
            have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
              fun type member => (expectedBelow type member).weaken argumentsProperties.1.next_le
            have expectedSafeAtArguments : ∀ type ∈ expected, Safe protectedVars argumentState type :=
              fun type member => argumentsPrivacy.1 _ (expectedSafe type member)
            have argumentBound : ∀ v ∈ protectedVars, v.index < argumentState.inference.next :=
              fun v member => Nat.lt_of_lt_of_le (bound v member) argumentsProperties.1.next_le
            have finishSelected (name : String) (candidates : List ProgramFunctionSignature)
                (subset : candidates ⊆ context.signatures.functions) (attempt : CandidateAttemptResult)
                (selectionSuccess : selectFunctionCandidateFrom context name candidates arguments
                  (relevantIntegerLiterals argumentState allocated.integerLiterals.length arguments) id expected argumentState = .ok attempt)
                (resultEq : recordSelectedCall expression callee name arguments attempt = result) :
                SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
                  LiveBindersSafe protectedVars result.2 ∧
                  ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
              have selected := selectFunctionCandidateFrom_private catalog subset argumentsProperties.2.1 argumentBound
                argumentsProperties.2.2 expectedAtArguments argumentsPrivacy.2.1 expectedSafeAtArguments argumentsPrivacy.2.2.1 selectionSuccess
              have recorded := recordSelectedCall_private expression callee name arguments attempt selected.2.1 selected.2.2.1
              rw [← resultEq]
              refine ⟨prefixPrivacy.trans (selected.1.trans recorded.1), recorded.2.1, recorded.2.2.1, ?_⟩
              have rows := new_requirements_trans argumentsPrivacy.2.2.2 selected.2.2.2 selected.1
              intro row member fresh type typeMember
              exact recorded.1 _ (rows row (recorded.2.2.2 ▸ member) fresh type typeMember)
            have finishIndirect (calleeResult : InferredExpression) (calleeState : State)
                (calleeSuccess : inferExprFuel fuel context callee none argumentState = .ok (calleeResult,calleeState))
                (application : IndirectApplicationResult)
                (applicationSuccess : applyFunctionType context id calleeResult.type arguments expected calleeState = .ok application)
                (resultEq : recordIndirectCall expression calleeResult arguments application = result) :
                SafeTransport protectedVars initial result.2 ∧ Safe protectedVars result.2 result.1.type ∧
                  LiveBindersSafe protectedVars result.2 ∧
                  ∀ row ∈ result.2.requirements, row ∉ initial.requirements → PredicateSafe protectedVars result.2 row.predicate := by
              have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1 validated canonical (by simp) calleeSuccess
              have calleePrivacy := calleeInduction argumentState argumentsProperties.2.1
                ((inferExprsFuel_direct_progress argumentsResult).wellFormed wellFormed) argumentBound argumentsPrivacy.2.2.1
                catalog validated canonical (by simp) (by simp) (calleeResult,calleeState) calleeSuccess
              have applied := applyFunctionType_private catalog calleeProperties.2.1
                (fun v member => Nat.lt_of_lt_of_le (argumentBound v member) calleeProperties.1.next_le)
                calleeProperties.2.2
                (fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le)
                (fun type member => (expectedAtArguments type member).weaken calleeProperties.1.next_le)
                calleePrivacy.2.1 (fun argument member => calleePrivacy.1 _ (argumentsPrivacy.2.1 argument member))
                (fun type member => calleePrivacy.1 _ (expectedSafeAtArguments type member)) calleePrivacy.2.2.1 applicationSuccess
              have recorded := recordIndirectCall_private expression calleeResult arguments application applied.2.1 applied.2.2.1
              rw [← resultEq]
              refine ⟨prefixPrivacy.trans (calleePrivacy.1.trans (applied.1.trans recorded.1)), recorded.2.1, recorded.2.2.1, ?_⟩
              have rows := new_requirements_trans
                (new_requirements_trans argumentsPrivacy.2.2.2 calleePrivacy.2.2.2 calleePrivacy.1) applied.2.2.2 applied.1
              intro row member fresh type typeMember
              exact recorded.1 _ (rows row (recorded.2.2.2 ▸ member) fresh type typeMember)
            cases qualifiedEq : calleeQualifiedIdentifier? callee with
            | some qualified =>
                rcases qualified with ⟨namespacePath, name⟩
                simp only [qualifiedEq] at success
                cases binderEq :
                    argumentState.lookupBinder? namespacePath.head! with
                | some binder =>
                    simp only [binderEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | none =>
                    simp only [binderEq] at success
                    cases functionsResult : qualifiedFunctionsNamed
                        context namespacePath name with
                    | error error =>
                        simp [functionsResult]
                          at success
                    | ok candidatesOption =>
                        simp only [functionsResult]
                          at success
                        cases candidatesOption with
                        | some candidates =>
                            cases selectionResult :
                                selectFunctionCandidateFrom context
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates arguments
                                  (relevantIntegerLiterals
                                    argumentState
                                    allocated.integerLiterals.length
                                    arguments)
                                  id expected argumentState with
                            | error error =>
                                simp [selectionResult] at success
                            | ok attempt =>
                                simp only [selectionResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishSelected
                                  (String.intercalate "."
                                    (namespacePath ++ [name]))
                                  candidates
                                  (qualifiedFunctionsNamed_success_subset_catalog
                                    functionsResult)
                                  attempt selectionResult resultEq
                        | none =>
                            cases calleeResult : inferExprFuel fuel
                                context callee none argumentState with
                            | error error =>
                                simp [calleeResult]
                                  at success
                            | ok calleePair =>
                                rcases calleePair with
                                  ⟨inferredCallee, calleeState⟩
                                simp only [calleeResult] at success
                                cases applicationResult :
                                    applyFunctionType context id
                                      inferredCallee.type arguments
                                      expected calleeState with
                                | error error =>
                                    simp [applicationResult] at success
                                | ok application =>
                                    simp only [applicationResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishIndirect inferredCallee
                                      calleeState calleeResult
                                      application applicationResult
                                      resultEq
            | none =>
                simp only [qualifiedEq] at success
                cases identifierEq : calleeIdentifier? callee with
                | none =>
                    simp only [identifierEq] at success
                    cases calleeResult : inferExprFuel fuel context callee
                        none argumentState with
                    | error error =>
                        simp [calleeResult] at success
                    | ok calleePair =>
                        rcases calleePair with
                          ⟨inferredCallee, calleeState⟩
                        simp only [calleeResult] at success
                        cases applicationResult : applyFunctionType
                            context id inferredCallee.type arguments
                            expected calleeState with
                        | error error =>
                            simp [applicationResult]
                              at success
                        | ok application =>
                            simp only [applicationResult, pure, Pure.pure, Except.pure]
                              at success
                            injection success with resultEq
                            exact finishIndirect inferredCallee
                              calleeState calleeResult application
                              applicationResult resultEq
                | some name =>
                    simp only [identifierEq] at success
                    cases binderEq : argumentState.lookupBinder? name with
                    | some binder =>
                        simp only [binderEq] at success
                        cases calleeResult : inferExprFuel fuel context
                            callee none argumentState with
                        | error error =>
                            simp [calleeResult]
                              at success
                        | ok calleePair =>
                            rcases calleePair with
                              ⟨inferredCallee, calleeState⟩
                            simp only [calleeResult] at success
                            cases applicationResult : applyFunctionType
                                context id inferredCallee.type arguments
                                expected calleeState with
                            | error error =>
                                simp [applicationResult] at success
                            | ok application =>
                                simp only [applicationResult, pure, Pure.pure,
                                  Except.pure] at success
                                injection success with resultEq
                                exact finishIndirect inferredCallee
                                  calleeState calleeResult application
                                  applicationResult resultEq
                    | none =>
                        simp only [binderEq] at success
                        cases functionsResult : functionsNamed context
                            name with
                        | error error =>
                            simp [functionsResult]
                              at success
                        | ok candidates =>
                            simp only [functionsResult] at success
                            cases candidates with
                            | nil =>
                                cases builtinEq :
                                    builtinFunctionNamed? name with
                                | none =>
                                    simp [builtinEq] at success
                                | some function =>
                                    simp only [builtinEq] at success
                                    have builtinPrivacy := recordBuiltinFunctionCall_private
                                      argumentsPrivacy.2.1 expectedSafeAtArguments argumentsPrivacy.2.2.1 success
                                    refine ⟨prefixPrivacy.trans builtinPrivacy.1, builtinPrivacy.2.1,
                                      builtinPrivacy.2.2.1, ?_⟩
                                    intro row member fresh
                                    have inArguments := builtinPrivacy.2.2.2 ▸ member
                                    exact fun type typeMember => builtinPrivacy.1 _
                                      (argumentsPrivacy.2.2.2 row inArguments fresh type typeMember)
                            | cons candidate rest =>
                                cases selectionResult :
                                    selectFunctionCandidateFrom context
                                      name (candidate :: rest) arguments
                                      (relevantIntegerLiterals
                                        argumentState
                                        allocated.integerLiterals.length
                                        arguments)
                                      id expected argumentState with
                                | error error =>
                                    simp [selectionResult] at success
                                | ok attempt =>
                                    simp only [selectionResult, pure, Pure.pure,
                                      Except.pure] at success
                                    injection success with resultEq
                                    exact finishSelected name
                                      (candidate :: rest)
                                      (functionsNamed_success_subset_catalog
                                        functionsResult)
                                      attempt selectionResult resultEq

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
