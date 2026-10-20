import Solcore.SourceSemantics.SourceInferenceNormalizedCallFormation
import Solcore.SourceSemantics.SourceInferenceNormalizedConstructorDispatch

/-! The actual call dispatch connects smaller constructor, argument and callee
inference receipts to the same final substitution and capture checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

theorem inferExprFuel_call_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat} {context : SourceInference.Context}
    {expression callee : Syntax.Expr} {sourceArguments : Syntax.DelimitedList Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (expressionEq : expression.value = .call callee sourceArguments)
    (constructorInduction : ∀ instantiation state,
      InferConstructorApplicationFuelFormation semantic outer fuel context expression
        initial.allocateExpressionId.1 instantiation sourceArguments.elements expected state)
    (argumentsInduction : InferExprsFuelFormation semantic outer fuel context
      sourceArguments.elements initial.allocateExpressionId.2)
    (calleeInduction : ∀ state, InferExprFuelFormation semantic outer fuel context callee none state) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id,allocated) := rfl
  have allocatedReady : allocated.InferenceReady := State.InferenceReady.allocateExpressionId ready
  have allocatedNodes := State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes
  have allocatedFormed : NormalizedStateFormation semantic outer allocated := formed.congr rfl rfl
  unfold inferExprFuel at success
  simp only [allocationEq,expressionEq,bind,Except.bind] at success
  cases candidatesResult : constructorCalleeCandidates context allocated callee with
  | error error => simp [candidatesResult] at success
  | ok candidates =>
    simp only [candidatesResult] at success
    cases candidates with
    | cons candidate rest =>
      cases rest with
      | cons second tail => simp at success
      | nil =>
        rcases candidate with ⟨dataType,constructor⟩
        let fresh := freshDataConstructorInstantiation dataType constructor allocated
        have members := constructorCalleeCandidates_success_members candidatesResult dataType constructor (by simp)
        have freshProperties := freshDataConstructorInstantiation_inferenceProperties dataType constructor allocated allocatedReady
          (formation.validated.data_constructor_payloadTypes_variablesBelow members.1 members.2 _)
        have freshFormed := fresh_constructor_normalized_formation formation allocatedFormed members.1 members.2
        have freshNodes := (freshDataConstructorInstantiation_occurrenceBoundExtends dataType constructor allocated).nodesBelowNextOccurrence allocatedNodes
        exact constructorInduction fresh.1 fresh.2 freshProperties.2.1 freshNodes freshFormed.1 formation
          freshProperties.2.2.2.1 freshFormed.2.1 freshProperties.2.2.2.2 freshFormed.2.2
          (fun type member => (expectedBelow type member).weaken freshProperties.1.next_le)
          expectedFormed result success continuation capture
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
            rcases argumentsPair with ⟨arguments,argumentState⟩
            simp only [argumentsResult] at success
            have argumentsProperties := inferExprsFuel_inferenceProperties allocatedReady formation.validated formation.functionShapes argumentsResult
            have argumentNodes := (inferExprsFuel_occurrenceBoundExtends argumentsResult).nodesBelowNextOccurrence allocatedNodes
            have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
              fun type member => (expectedBelow type member).weaken argumentsProperties.1.next_le
            have finishSelected (name : String) (candidates : List ProgramFunctionSignature)
                (subset : candidates ⊆ context.signatures.functions) (attempt : CandidateAttemptResult)
                (selectionSuccess : selectFunctionCandidateFrom context name candidates arguments
                  (relevantIntegerLiterals argumentState allocated.integerLiterals.length arguments) id expected argumentState = .ok attempt)
                (resultEq : recordSelectedCall expression callee name arguments attempt = result) :
                TypeAdmissible semantic (outer.apply result.1.type) ∧ NormalizedStateFormation semantic outer result.2 := by
              have fields := recordSelectedCallResult_normalized_fields expression callee name arguments attempt attempt.result [] attempt.state
              have recordedEq : recordSelectedCallResult expression callee name arguments attempt attempt.result [] attempt.state = result := resultEq
              rw [recordedEq] at fields
              have attemptContinuation : outer.SemanticallyExtends attempt.state.inference.substitution := by
                rwa [fields.1] at continuation
              have selectedProperties := selectFunctionCandidateFrom_inferenceProperties argumentsProperties.2.1
                argumentsProperties.2.2
                (fun signature member => formation.validated.function_scheme_body_variablesBelow (subset member) (formation.functionShapes signature (subset member)) _)
                expectedAtArguments selectionSuccess
              have argumentContinuation := attemptContinuation.trans selectedProperties.1.substitution_extends
              have argumentCapture : NoCaptureNodes outer argumentState.nodes := by
                unfold NoCaptureNodes at capture ⊢
                rw [fields.2.2.2.2,(selectFunctionCandidateFrom_occurrenceState_eq selectionSuccess).1] at capture
                exact capture
              have argumentFormation := argumentsInduction allocatedReady allocatedNodes allocatedFormed formation
                (arguments,argumentState) argumentsResult argumentContinuation argumentCapture
              have selected := selectFunctionCandidateFrom_normalized_formation formation argumentFormation.2 subset
                argumentsProperties.2.1 argumentsProperties.2.2 expectedAtArguments
                argumentFormation.1 expectedFormed attemptContinuation selectionSuccess
              exact ⟨fields.2.2.2.1 ▸ selected.1, selected.2.congr fields.2.1 fields.2.2.1⟩
            have finishIndirect (calleeResult : InferredExpression) (calleeState : State)
                (calleeSuccess : inferExprFuel fuel context callee none argumentState = .ok (calleeResult,calleeState))
                (application : IndirectApplicationResult)
                (applicationSuccess : applyFunctionType context id calleeResult.type arguments expected calleeState = .ok application)
                (resultEq : recordIndirectCall expression calleeResult arguments application = result) :
                TypeAdmissible semantic (outer.apply result.1.type) ∧ NormalizedStateFormation semantic outer result.2 := by
              have fields := recordIndirectCall_normalized_fields expression calleeResult arguments application
              rw [resultEq] at fields
              have applicationContinuation : outer.SemanticallyExtends application.state.inference.substitution := by
                rwa [fields.1] at continuation
              have calleeProperties := inferExprFuel_inferenceProperties argumentsProperties.2.1 formation.validated formation.functionShapes (by simp) calleeSuccess
              have argsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow calleeState.inference.next :=
                fun argument member => (argumentsProperties.2.2 argument member).weaken calleeProperties.1.next_le
              have expectedBelowCallee : ∀ type ∈ expected, type.VariablesBelow calleeState.inference.next :=
                fun type member => (expectedAtArguments type member).weaken calleeProperties.1.next_le
              have appliedProperties := applyFunctionType_inferenceProperties calleeProperties.2.1 calleeProperties.2.2
                argsBelow expectedBelowCallee applicationSuccess
              have calleeContinuation := applicationContinuation.trans appliedProperties.1.substitution_extends
              have argumentContinuation := calleeContinuation.trans calleeProperties.1.substitution_extends
              have calleeCapture : NoCaptureNodes outer calleeState.nodes := by
                unfold NoCaptureNodes at capture ⊢
                rw [fields.2.2.2.2,(applyFunctionType_occurrenceState_eq applicationSuccess).1] at capture
                exact capture
              have retained : argumentState.nodes <+: calleeState.nodes :=
                inferExprFuel_preserves_nodesPrefix calleeSuccess (List.prefix_refl _) argumentNodes (Nat.le_refl _)
              have argumentFormation := argumentsInduction allocatedReady allocatedNodes allocatedFormed formation
                (arguments,argumentState) argumentsResult argumentContinuation (calleeCapture.of_prefix retained)
              have calleeFormation := calleeInduction argumentState argumentsProperties.2.1 argumentNodes argumentFormation.2 formation
                (by simp) (by simp) (calleeResult,calleeState) calleeSuccess calleeContinuation calleeCapture
              have applied := applyFunctionType_normalized_formation formation.toFormationContext formation.scope.binders
                calleeProperties.2.1 calleeProperties.2.2 argsBelow expectedBelowCallee calleeFormation.1
                argumentFormation.1 expectedFormed applicationContinuation applicationSuccess
              have applicationFormed := calleeFormation.2.of_new_rows
                (congrArg LexicalScope.binders (localReadScope_applyFunctionType_lexicalScope applicationSuccess)) applied.2
              exact ⟨fields.2.2.2.1 ▸ applied.1, applicationFormed.congr fields.2.1 fields.2.2.1⟩
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
                                    have builtinProperties := recordBuiltinFunctionCall_inferenceProperties
                                      argumentsProperties.2.1 argumentsProperties.2.2 expectedAtArguments success
                                    have argumentContinuation := continuation.trans builtinProperties.1.substitution_extends
                                    have fields := recordBuiltinFunctionCall_normalized_fields success
                                    have argumentCapture : NoCaptureNodes outer argumentState.nodes := by
                                      unfold NoCaptureNodes at capture ⊢
                                      rwa [fields.2.2] at capture
                                    have argumentFormation := argumentsInduction allocatedReady allocatedNodes allocatedFormed formation
                                      (arguments,argumentState) argumentsResult argumentContinuation argumentCapture
                                    exact recordBuiltinFunctionCall_normalized_formation formation argumentFormation.2 success
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


end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
