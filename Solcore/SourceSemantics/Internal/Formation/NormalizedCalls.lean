import Solcore.SourceSemantics.Internal.Formation.NormalizedDeclarations
import Solcore.Frontend.SourceInference.Internal.OccurrenceProperties
import Solcore.SourceSemantics.Internal.Formation.NormalizedCoercions
import Solcore.SourceSemantics.Internal.Formation.NormalizedMatches
import Solcore.SourceSemantics.Internal.Formation.NormalizedLambdas

/-!
# Normalized calls

Continuations of calls, constructors, initializers and operators, ending in the recursive inference
theorem.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedCallContinuation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedConstructorContinuation
/-! Normalized formation follows the actual constructor argument traversal.
The final substitution and capture facts are passed backwards only through
successful child calls and their real node inventories. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness

private theorem unify_fields {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    after.localBinders = before.localBinders ∧ after.requirements = before.requirements := by
  unfold Detail.unify at accepted
  cases unified : before.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] at accepted
    cases accepted
    exact ⟨rfl,rfl⟩

private theorem recording_noCapture
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State}
    {outer : Substitution}
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state localSchemeInstantiationStart = .ok result)
    (capture : NoCaptureNodes outer result.2.nodes) : NoCaptureNodes outer state.nodes := by
  obtain ⟨fitted, fit, _, nodes⟩ := recordExpressionWithExpected_success_nodes accepted
  rw [nodes, (withExpected_occurrenceState_eq fit).1] at capture
  exact capture.of_prefix (List.prefix_append _ _)

private theorem recording_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State}
    {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer)
    (stateFormed : NormalizedStateFormation semantic outer state)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (typeFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state localSchemeInstantiationStart = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have produced := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation typeFormed expectedFormed accepted
  exact ⟨produced.1,stateFormed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_recordExpressionWithExpected_lexicalScope accepted)) produced.2⟩

/-- The accepted cons branch exposes its actual head and tail. The final
capture checks for the head are recovered from the tail's retained prefix. -/
theorem inferConstructorArgumentsFuel_cons_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
    {expected : Ty} {expectedTypes : List Ty} {initial : State}
    (sourceIH : InferExprFuelFormation semantic outer fuel context source
      (some (initial.resolve expected)) initial)
    (tailIH : ∀ state, InferConstructorArgumentsFuelFormation semantic outer fuel
      context sources expectedTypes state) :
    InferConstructorArgumentsFuelFormation semantic outer fuel context
      (source :: sources) (expected :: expectedTypes) initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation capture
  unfold inferConstructorArgumentsFuel at success
  cases sourceRun : inferExprFuel fuel context source (some (initial.resolve expected)) initial with
  | error error => simp [sourceRun, bind, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨inferred,sourceState⟩
    simp only [sourceRun,bind,Except.bind] at success
    cases tailRun : inferConstructorArgumentsFuel fuel context sources expectedTypes sourceState with
    | error error => simp [tailRun] at success
    | ok pair =>
      rcases pair with ⟨tail,finalState⟩
      simp only [tailRun] at success
      cases success
      have expectedTypeBelow := expectedBelow expected (by simp)
      have fitBelow : ∀ type ∈ some (initial.resolve expected), type.VariablesBelow initial.inference.next := by
        intro type member
        cases Option.mem_def.mp member
        exact ready.solved.variablesBelow_apply expectedTypeBelow
      have sourceProperties := inferExprFuel_inferenceProperties ready formation.validated formation.functionShapes fitBelow sourceRun
      have tailBelow : ∀ type ∈ expectedTypes, type.VariablesBelow sourceState.inference.next := by
        intro type member
        exact (expectedBelow type (by simp [member])).weaken sourceProperties.1.next_le
      have tailProperties := inferConstructorArgumentsFuel_inferenceProperties sourceProperties.2.1
        formation.validated formation.functionShapes tailBelow tailRun
      have sourceContinuation := continuation.trans tailProperties.1.substitution_extends
      have initialContinuation := sourceContinuation.trans sourceProperties.1.substitution_extends
      have fitFormed : ∀ type ∈ some (initial.resolve expected), TypeAdmissible semantic (outer.apply type) := by
        intro type member
        cases Option.mem_def.mp member
        exact (initialContinuation expected).symm ▸ expectedFormed expected (by simp)
      have sourceNodes := (inferExprFuel_occurrenceBoundExtends sourceRun).nodesBelowNextOccurrence nodes
      have retained : sourceState.nodes <+: finalState.nodes :=
        inferConstructorArgumentsFuel_preserves_nodesPrefix tailRun
          (List.prefix_refl _) sourceNodes (Nat.le_refl _)
      have sourceCapture := capture.of_prefix retained
      have headFormation := sourceIH ready nodes formed formation fitBelow fitFormed
        _ sourceRun sourceContinuation sourceCapture
      have tailFormation := tailIH sourceState sourceProperties.2.1 sourceNodes headFormation.2 formation
        tailBelow (fun type member => expectedFormed type (by simp [member])) _ tailRun continuation capture
      refine ⟨?_,tailFormation.2⟩
      intro element member
      rcases List.mem_cons.mp member with rfl | member
      · exact headFormation.1
      · exact tailFormation.1 element member

/-- Actual result fitting precedes the ordered constructor argument traversal;
recording uses the final continuation of the same successful execution. -/
theorem inferConstructorApplicationFuel_formation
    {semantic : SourceSemantics.Context} {outer : Substitution} {fuel : Nat}
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {instantiation : DataConstructorInstantiation} {arguments : List Syntax.Expr}
    {expected : Option Ty} {initial : State}
    (argumentsIH : ∀ state, InferConstructorArgumentsFuelFormation semantic outer fuel
      context arguments instantiation.payloadTypes state) :
    InferConstructorApplicationFuelFormation semantic outer fuel context source id
      instantiation arguments expected initial := by
  intro ready nodes formed formation payloadBelow payloadFormed resultBelow resultFormed
    expectedBelow expectedFormed result success continuation capture
  unfold inferConstructorApplicationFuel at success
  by_cases arity : arguments.length = instantiation.payloadTypes.length
  · simp only [arity,bind,Except.bind] at success
    cases expected with
    | none =>
      simp only [pure,Pure.pure,Except.pure] at success
      cases argumentsRun : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes initial with
      | error error => simp [argumentsRun] at success
      | ok pair =>
        rcases pair with ⟨inferredArguments,argumentsState⟩
        simp only [argumentsRun] at success
        have properties := inferConstructorArgumentsFuel_inferenceProperties ready
          formation.validated formation.functionShapes payloadBelow argumentsRun
        have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1
          (properties.1.resolve_variablesBelow resultBelow) (by simp) success
        have argumentsContinuation := continuation.trans recordProperties.1.substitution_extends
        have argumentsFormation := argumentsIH initial ready nodes formed formation payloadBelow payloadFormed
          _ argumentsRun argumentsContinuation (recording_noCapture success capture)
        apply recording_formation formation argumentsFormation.2 continuation _ (by simp) success
        exact (argumentsContinuation instantiation.resultType).symm ▸ resultFormed
    | some expectedType =>
      cases fittedRun : Detail.unify initial instantiation.resultType expectedType with
      | error error => simp [fittedRun] at success
      | ok fittedState =>
        simp only [fittedRun] at success
        have fittedProperties := unify_inferenceProgress ready.solved resultBelow
          (expectedBelow expectedType (by simp)) fittedRun
        have fittedReady := unify_preserves_inferenceReady ready resultBelow
          (expectedBelow expectedType (by simp)) fittedRun
        have fittedNodes := (unify_occurrenceBoundExtends fittedRun).nodesBelowNextOccurrence nodes
        have fittedFields := unify_fields fittedRun
        have fittedFormed := formed.congr fittedFields.1 fittedFields.2
        have payloadAtFitted : ∀ type ∈ instantiation.payloadTypes, type.VariablesBelow fittedState.inference.next :=
          fun type member => (payloadBelow type member).weaken fittedProperties.next_le
        cases argumentsRun : inferConstructorArgumentsFuel fuel context arguments instantiation.payloadTypes fittedState with
        | error error => simp [argumentsRun] at success
        | ok pair =>
          rcases pair with ⟨inferredArguments,argumentsState⟩
          simp only [argumentsRun] at success
          have properties := inferConstructorArgumentsFuel_inferenceProperties fittedReady
            formation.validated formation.functionShapes payloadAtFitted argumentsRun
          have throughArguments := fittedProperties.trans properties.1
          have expectedAtArguments : ∀ type ∈ some expectedType, type.VariablesBelow argumentsState.inference.next :=
            fun type member => (expectedBelow type member).weaken throughArguments.next_le
          have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1
            (throughArguments.resolve_variablesBelow resultBelow) expectedAtArguments success
          have argumentsContinuation := continuation.trans recordProperties.1.substitution_extends
          have argumentsFormation := argumentsIH fittedState fittedReady fittedNodes fittedFormed formation
            payloadAtFitted payloadFormed _ argumentsRun argumentsContinuation (recording_noCapture success capture)
          apply recording_formation formation argumentsFormation.2 continuation _ expectedFormed success
          exact (argumentsContinuation instantiation.resultType).symm ▸ resultFormed
  · simp [arity,bind,Except.bind] at success

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedInitializedContinuation
/-! The recursive initializer result and its exact executable allocation
compose at the real initialized-let boundary, including for-header metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail

theorem annotation_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {source : Option Syntax.TypeExpr} {expected : Option Ty}
    (formation : InferenceFormationContext semantic context outer)
    (annotation : LocalLetRequirementTiming.Annotation context source expected) (next : Nat) :
    (∀ type ∈ expected, type.VariablesBelow next) ∧
      ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type) := by
  cases annotation with
  | none => simp
  | @some syntaxType type accepted =>
    constructor
    · intro selected member
      cases Option.mem_some_iff.mp member
      exact resolveSourceType_success_variablesBelow accepted next
    · intro selected member
      cases Option.mem_some_iff.mp member
      rw [resolveSourceType_success_apply_eq_self outer accepted]
      exact TypeAdmissible.ofWellFormed
        (resolveSourceType_success_typeWellFormed formation.canonical
          formation.signatures formation.scope.parameters formation.scope.owner accepted)

theorem uninitialized_binding_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {source : Syntax.TypeExpr} {type : Ty}
    {state : State} (name : Syntax.Identifier)
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (accepted : resolveSourceType context source = .ok type)
    (continuation : outer.SemanticallyExtends state.inference.substitution) :
    let locals := state.binderEnvironment.apply state.inference.substitution
    let generalized := generalizeValue state locals state.nextRequirement (state.resolve type)
    NormalizedStateFormation semantic outer
      ((state.withLocals locals).allocateBinder name.value generalized.scheme
        (some name.span) false generalized.requirements).2 := by
  dsimp only
  let locals := state.binderEnvironment.apply state.inference.substitution
  have resolvedEq : state.resolve type = type :=
    resolveSourceType_success_apply_eq_self state.inference.substitution accepted
  have closed : type.freeVariables = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro metavariable member
    exact Nat.not_lt_zero _ (resolveSourceType_success_variablesBelow accepted 0 metavariable member)
  have quantifiedEmpty :
      (generalizeValue state locals state.nextRequirement (state.resolve type)).scheme.quantified = [] := by
    rw [generalizeValue_scheme_quantified, resolvedEq, closed]
    rfl
  have typeFormed : TypeAdmissible semantic (outer.apply (state.resolve type)) := by
    rw [resolvedEq, resolveSourceType_success_apply_eq_self outer accepted]
    exact TypeAdmissible.ofWellFormed
      (resolveSourceType_success_typeWellFormed formation.canonical
        formation.signatures formation.scope.parameters formation.scope.owner accepted)
  have localsFormed : NormalizedStateFormation semantic outer (state.withLocals locals) :=
    formed.congr rfl rfl
  apply NormalizedStateFormation.allocate localsFormed
  apply NormalizedBinderFormation.generalized locals state.nextRequirement name.value
    (some name.span) false continuation typeFormed formed.requirements
  exact LocalBinderInstantiationNoCapture.of_quantified_eq_nil quantifiedEmpty

theorem initialized_statement_receipt_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (child : InferExprFuelFormation semantic outer fuel context receipt.initializer
      receipt.expected initial.allocateStatementId.2)
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial)
    (formation : InferenceFormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (captures : NoCaptureNodes outer result.state.nodes) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  have sameInference : result.state.inference = receipt.ready.inference :=
    congrArg (fun value : StatementResult => value.state.inference) receipt.completed
  have childContinuation : outer.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [sameInference] at continuation
  have childCaptures : NoCaptureNodes outer receipt.ready.nodes :=
    captures.mono (by intro node member; rw [receipt.completed]; exact List.mem_append_left _ member)
  have expected := annotation_normalized_formation formation receipt.annotationAccepted
    initial.allocateStatementId.2.inference.next
  have childFormation := child (State.InferenceReady.allocateStatementId ready)
    (State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodes)
    (formed.congr rfl rfl) formation expected.1 expected.2
    (receipt.value, receipt.ready) receipt.child childContinuation childCaptures
  have newCapture : LocalBinderInstantiationNoCapture outer receipt.binding.1 :=
    captures.at_statement receipt.recorded _ (List.mem_singleton_self _)
  have installed := initialized_statement_normalized_formation receipt childFormation.2 childFormation.1
    childContinuation newCapture
  refine ⟨?_, installed.2⟩
  rw [receipt.completed]
  exact .unit formation.scope.binders

theorem initialized_header_receipt_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {item : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result)
    (child : InferExprFuelFormation semantic outer fuel context receipt.initializer receipt.expected initial)
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial)
    (formation : InferenceFormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (captures : NoCaptureNodes outer result.2.nodes)
    (headerCaptures : NoCaptureItems outer [result.1]) :
    NormalizedStateFormation semantic outer result.2 := by
  have sameInference : result.2.inference = receipt.ready.inference :=
    congrArg (fun value : ForItemForm × State => value.2.inference) receipt.completed
  have childContinuation : outer.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [sameInference] at continuation
  have childCaptures : NoCaptureNodes outer receipt.ready.nodes := by
    rw [receipt.completed] at captures
    exact captures
  have expected := annotation_normalized_formation formation receipt.annotationAccepted initial.inference.next
  have childFormation := child ready nodes formed formation expected.1 expected.2
    (receipt.value, receipt.ready) receipt.child childContinuation childCaptures
  have newCapture : LocalBinderInstantiationNoCapture outer receipt.binding.1 := by
    apply headerCaptures
    rw [receipt.recorded]
    exact List.mem_flatMap.mpr ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩
  exact (initialized_header_normalized_formation receipt childFormation.2 childFormation.1
    childContinuation newCapture).2

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedLookupBranch
/-! The actual local-reference branch uses only the earlier structural binder
invariant. Ledger identity receipts are unnecessary for predicate formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

private theorem normalized_predicate {outer : Substitution} {state : State}
    (continuation : outer.SemanticallyExtends state.inference.substitution)
    (predicate : ProgramPredicate) :
    TypedTraitResolution.applySubstitution outer (Detail.applyPredicate state predicate) =
      TypedTraitResolution.applySubstitution outer predicate := by
  cases predicate with
  | mk trait subject arguments =>
    simp only [Detail.applyPredicate, TypedTraitResolution.applySubstitution]
    congr 1
    · exact continuation subject
    · simp only [List.map_map]
      exact List.map_congr_left (fun type _ => continuation type)

private theorem batch_origin (state : State) (predicates : List ProgramPredicate)
    {row : Requirement} (member : row ∈ (state.addRequirementsWithIds predicates).2.requirements) :
    row ∈ state.requirements ∨ row.predicate ∈ predicates := by
  induction predicates generalizing state with
  | nil => exact Or.inl member
  | cons predicate predicates ih =>
    rcases ih (state.addRequirementWithId predicate).2 member with old | issued
    · rcases List.mem_append.mp old with old | new
      · exact .inl old
      · cases List.mem_singleton.mp new
        exact .inr (by simp)
    · exact .inr (by simp [issued])

theorem inferExprFuel_local_normalized_state
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {name : Syntax.Identifier} {expected : Option Ty}
    {initial allocated : State} {id : ExpressionId}
    {binder : TypedBinder} {result : InferredExpression × State}
    (formation : InferenceFormationContext semantic context outer)
    (ready : initial.InferenceReady)
    (earlier : NormalizedStateFormation semantic outer initial)
    (form : expression.value = .identifier name)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (found : allocated.lookupBinder? name.value = some binder)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.inferExprFuel (fuel + 1) context expression expected initial = .ok result)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have member := (State.lookupBinder?_eq_some_facts found).1
  rw [allocatedEq] at member
  have binderFormed := earlier.binders binder member
  let instantiation := binder.scheme.instantiateWithSubstitution allocated.inference.next
  let advanced : State := {allocated with inference := {allocated.inference with next := instantiation.next}}
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiation.substitution requirement.predicate)
  let batch := advanced.addRequirementsWithIds predicates
  have progress := Detail.inferExprFuel_inferenceProperties ready formation.validated
    formation.functionShapes expectedBelow accepted
  have beforeContinuation : outer.SemanticallyExtends advanced.inference.substitution := by
    have before := continuation.trans progress.1.substitution_extends
    change outer.SemanticallyExtends allocated.inference.substitution
    rw [allocatedEq]
    exact before
  have instantiated := binderFormed.instantiate formation.toFormationContext
    formation.scope.binders allocated.inference.next
  have bodyFormed : TypeAdmissible semantic (outer.apply (advanced.resolve instantiation.body)) :=
    (beforeContinuation _).symm ▸ instantiated.1
  have predicatesFormed : ∀ predicate ∈ predicates,
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer predicate) := by
    intro predicate present
    obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp present
    rw [normalized_predicate beforeContinuation]
    exact instantiated.2 requirement requirementMember
  have recorded := Detail.inferExprFuel_success_localIdentifier_record form allocation found accepted
  have fitted := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation bodyFormed expectedFormed recorded
  refine ⟨fitted.1, earlier.of_new_rows
    (congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)) ?_⟩
  apply new_normalized_requirements_trans (middle := batch.2) ?_ fitted.2
  intro row present fresh
  rcases batch_origin advanced predicates present with old | issued
  · have original : row ∈ initial.requirements := by
      change row ∈ allocated.requirements at old
      rw [allocatedEq] at old
      exact old
    exact (fresh original).elim
  · exact predicatesFormed row.predicate issued

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedRecordingContinuation
/-! Recording joins a real expression result to its actual expected fit.
Capture facts are restricted through the exact recorded node table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail

theorem expression_allocation_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial) :
    allocated.InferenceReady ∧ allocated.NodesBelowNextOccurrence ∧
      NormalizedStateFormation semantic outer allocated ∧
      allocated.inference = initial.inference := by
  have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact ⟨State.InferenceReady.allocateExpressionId ready,
    State.allocateExpressionId_preserves_nodesBelowNextOccurrence initial nodes,
    formed.congr rfl rfl, rfl⟩

theorem statement_allocation_normalized
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (ready : initial.InferenceReady) (nodes : initial.NodesBelowNextOccurrence)
    (formed : NormalizedStateFormation semantic outer initial) :
    allocated.InferenceReady ∧ allocated.NodesBelowNextOccurrence ∧
      NormalizedStateFormation semantic outer allocated ∧
      allocated.inference = initial.inference := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  rw [same]
  exact ⟨State.InferenceReady.allocateStatementId ready,
    State.allocateStatementId_preserves_nodesBelowNextOccurrence initial nodes,
    formed.congr rfl rfl, rfl⟩

theorem NoCaptureNodes.before_recordNode
    {outer : Substitution} {state : State} {node : Node}
    (capture : NoCaptureNodes outer (state.recordNode node).nodes) :
    NoCaptureNodes outer state.nodes :=
  capture.of_prefix (List.prefix_append _ _)

theorem NormalizedStateFormation.recordNode
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {state : State} (formed : NormalizedStateFormation semantic outer state) (node : Node) :
    NormalizedStateFormation semantic outer (state.recordNode node) :=
  formed.congr rfl rfl

theorem NormalizedStateFormation.unify
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {before after : State} {left right : Ty}
    (formed : NormalizedStateFormation semantic outer before)
    (accepted : Detail.unify before left right = .ok after) :
    NormalizedStateFormation semantic outer after :=
  formed.congr (congrArg LexicalScope.binders (unify_preserves_lexicalScope accepted))
    (unify_requirements_eq accepted)

theorem NoCaptureNodes.before_unify
    {outer : Substitution} {before after : State} {left right : Ty}
    (capture : NoCaptureNodes outer after.nodes)
    (accepted : Detail.unify before left right = .ok after) :
    NoCaptureNodes outer before.nodes := by
  rwa [(unify_occurrenceState_eq accepted).1] at capture

theorem NoCaptureNodes.before_recordExpressionWithExpected
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {requirements : List RequirementId}
    {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (capture : NoCaptureNodes outer result.2.nodes)
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    NoCaptureNodes outer state.nodes := by
  obtain ⟨fitted, fit, _, nodes⟩ := recordExpressionWithExpected_success_nodes accepted
  rw [nodes, (withExpected_occurrenceState_eq fit).1] at capture
  exact capture.of_prefix (List.prefix_append _ _)

theorem recordExpressionWithExpected_normalized_state
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (typeFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have produced := recordExpressionWithExpected_normalized_formation formation.toFormationContext
    continuation typeFormed expectedFormed accepted
  exact ⟨produced.1, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_recordExpressionWithExpected_lexicalScope accepted)) produced.2⟩

theorem normalized_productMany
    {semantic : SourceSemantics.Context} {outer : Substitution} {types : List Ty}
    (binders : TypeParameterBindersWellFormed semantic)
    (formed : ∀ type ∈ types, TypeAdmissible semantic (outer.apply type)) :
    TypeAdmissible semantic (outer.apply (Ty.productMany types)) := by
  rw [Substitution.apply_productMany]
  apply TypeAdmissible.productMany binders
  intro type member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact formed original present

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedOperatorContinuation
/-! Actual operator outputs are either closed builtin types or the actual
resolved operand. Their predicates use the same final substitution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation

set_option maxHeartbeats 800000 in
private theorem unary_result_shape
    {context : SourceInference.Context} {operator : Syntax.UnaryOp}
    {operand : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : inferUnaryOperator context operator operand expected literals state = .ok result) :
    result.type = .bool ∨ result.type = .word ∨ result.type = result.state.resolve operand := by
  unfold inferUnaryOperator at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals simp_all [State.resolve]
  all_goals cases operator <;> simp_all

set_option maxHeartbeats 800000 in
private theorem binary_result_shape
    {context : SourceInference.Context} {operator : Syntax.BinaryOp}
    {left right : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (accepted : inferBinaryOperator context operator left right expected literals state = .ok result) :
    result.type = .bool ∨ result.type = .word ∨ result.type = result.state.resolve left := by
  unfold inferBinaryOperator binaryOperatorTail at accepted
  simp_all [bind, Except.bind]
  repeat' first | split at accepted
  all_goals try cases accepted
  all_goals simp_all [State.resolve]
  all_goals cases operator <;> simp_all [binaryBuiltinType]

theorem inferUnaryOperator_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp}
    {operand : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (operandFormed : TypeAdmissible semantic (outer.apply operand))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferUnaryOperator context operator operand expected literals state = .ok result) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  refine ⟨?_, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_inferUnaryOperator_lexicalScope accepted))
    (inferUnaryOperator_normalized_issuance formation.catalog formation.signatures operandFormed continuation accepted)⟩
  rcases unary_result_shape accepted with closed | closed | resolved
  · rw [closed]; exact .bool formation.scope.binders
  · rw [closed]; exact .word formation.scope.binders
  · rw [resolved]
    exact (continuation operand).symm ▸ operandFormed

theorem inferBinaryOperator_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp}
    {left right : Ty} {expected : Option Ty} {literals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (formation : InferenceFormationContext semantic context outer)
    (formed : NormalizedStateFormation semantic outer state)
    (leftFormed : TypeAdmissible semantic (outer.apply left))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : inferBinaryOperator context operator left right expected literals state = .ok result) :
    TypeAdmissible semantic (outer.apply result.type) ∧
      NormalizedStateFormation semantic outer result.state := by
  refine ⟨?_, formed.of_new_rows
    (congrArg LexicalScope.binders (localReadScope_inferBinaryOperator_lexicalScope accepted))
    (inferBinaryOperator_normalized_issuance formation.catalog formation.signatures leftFormed continuation accepted)⟩
  rcases binary_result_shape accepted with closed | closed | resolved
  · rw [closed]; exact .bool formation.scope.binders
  · rw [closed]; exact .word formation.scope.binders
  · rw [resolved]
    exact (continuation left).symm ▸ leftFormed

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedOperatorBranches
/-! Actual operator branches connect their recursive operands to either the
builtin/trait path or the selected named function. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation

private theorem selected_suffix
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {source callee : Syntax.Expr}
    {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression} {literals : List IntegerLiteralOrigin}
    {id : ExpressionId} {expected : Option Ty} {state : State}
    {attempt : CandidateAttemptResult} {result : InferredExpression × State}
    (formation : InferenceFormationContext semantic context outer)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (cataloged : candidates ⊆ context.signatures.functions)
    (selected : selectFunctionCandidateFrom context name candidates arguments literals id expected state = .ok attempt)
    (recorded : recordSelectedCall source callee name arguments attempt = result)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (captures : NoCaptureNodes outer result.2.nodes)
    (earlier : outer.SemanticallyExtends state.inference.substitution →
      NoCaptureNodes outer state.nodes →
      (∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type)) ∧
        NormalizedStateFormation semantic outer state) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      NormalizedStateFormation semantic outer result.2 := by
  have fields := recordSelectedCallResult_normalized_fields source callee name arguments attempt
    attempt.result [] attempt.state
  have recordEq : recordSelectedCallResult source callee name arguments attempt attempt.result [] attempt.state = result := recorded
  rw [recordEq] at fields
  have selectedContinuation : outer.SemanticallyExtends attempt.state.inference.substitution := by
    rwa [fields.1] at continuation
  have properties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
    (fun signature member => formation.validated.function_scheme_body_variablesBelow
      (cataloged member) (formation.functionShapes signature (cataloged member)) _) expectedBelow selected
  have stateCapture : NoCaptureNodes outer state.nodes := by
    unfold NoCaptureNodes at captures ⊢
    rw [fields.2.2.2.2, (selectFunctionCandidateFrom_occurrenceState_eq selected).1] at captures
    exact captures
  have prior := earlier (selectedContinuation.trans properties.1.substitution_extends) stateCapture
  have produced := selectFunctionCandidateFrom_normalized_formation formation prior.2 cataloged
    ready argumentsBelow expectedBelow prior.1 expectedFormed selectedContinuation selected
  exact ⟨fields.2.2.2.1 ▸ produced.1, produced.2.congr fields.2.1 fields.2.2.1⟩

theorem inferExprFuel_unary_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {fuel : Nat} {expression operand : Syntax.Expr}
    {operator : Syntax.Located Syntax.UnaryOp} {expected : Option Ty} {initial : State}
    (form : expression.value = .unary operator operand)
    (operandIH : InferExprFuelFormation semantic outer fuel context operand none initial.allocateExpressionId.2) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id, allocated) := rfl
  have allocation := expression_allocation_normalized allocationEq ready nodes formed
  unfold inferExprFuel at success
  simp only [allocationEq, form, bind, Except.bind] at success
  cases operandRun : inferExprFuel fuel context operand none allocated with
  | error error => simp [operandRun] at success
  | ok pair =>
    rcases pair with ⟨operandValue, operandState⟩
    simp only [operandRun] at success
    have operandProperties := inferExprFuel_inferenceProperties allocation.1
      formation.validated formation.functionShapes (by simp) operandRun
    have expectedOperand : ∀ type ∈ expected, type.VariablesBelow operandState.inference.next :=
      fun type member => (expectedBelow type member).weaken operandProperties.1.next_le
    let literals := relevantIntegerLiterals operandState allocated.integerLiterals.length [operandValue]
    have earlier
        (operandContinuation : outer.SemanticallyExtends operandState.inference.substitution)
        (operandCapture : NoCaptureNodes outer operandState.nodes) :
        TypeAdmissible semantic (outer.apply operandValue.type) ∧
          NormalizedStateFormation semantic outer operandState :=
      operandIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        (by simp) (by simp) _ operandRun operandContinuation operandCapture
    have finish (inferred : OperatorInferenceResult)
        (operatorRun : inferUnaryOperator context operator.value operandValue.type expected literals operandState = .ok inferred)
        (recordRun : recordExpressionWithExpected context expression id inferred.type
          (.unary operator.value operandValue.id) inferred.requirements expected inferred.state = .ok result) :
        TypeAdmissible semantic (outer.apply result.1.type) ∧
          NormalizedStateFormation semantic outer result.2 := by
      have properties := inferUnaryOperator_inferenceProperties operandProperties.2.1
        operandProperties.2.2 expectedOperand operatorRun
      have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1 properties.2.2
        (fun type member => (expectedOperand type member).weaken properties.1.next_le) recordRun
      have operatorContinuation := continuation.trans recordProperties.1.substitution_extends
      have operandCapture : NoCaptureNodes outer operandState.nodes := by
        have captured := captures.before_recordExpressionWithExpected recordRun
        rwa [(inferUnaryOperator_occurrenceState_eq operatorRun).1] at captured
      have prior := earlier (operatorContinuation.trans properties.1.substitution_extends) operandCapture
      have produced := inferUnaryOperator_normalized_formation formation prior.2 prior.1 operatorContinuation operatorRun
      exact recordExpressionWithExpected_normalized_state formation produced.2 continuation produced.1 expectedFormed recordRun
    cases dispatch : unaryOperatorDispatch operator.value with
    | traitMethod traitName methodName =>
      simp only [dispatch] at success
      cases operatorRun : inferUnaryOperator context operator.value operandValue.type expected literals operandState with
      | error error => simp [literals, operatorRun] at success
      | ok inferred =>
        simp only [literals, operatorRun] at success
        exact finish inferred operatorRun success
    | function name =>
      simp only [dispatch] at success
      cases functionsRun : functionsNamed context name with
      | error error => simp [functionsRun] at success
      | ok candidates =>
        simp only [functionsRun] at success
        cases candidates with
        | nil =>
          cases operatorRun : inferUnaryOperator context operator.value operandValue.type expected literals operandState with
          | error error => simp [literals, operatorRun] at success
          | ok inferred =>
            simp only [literals, operatorRun] at success
            exact finish inferred operatorRun success
        | cons candidate rest =>
          cases selected : selectFunctionCandidateFrom context name (candidate :: rest)
              [operandValue] literals id expected operandState with
          | error error => simp [literals, selected] at success
          | ok attempt =>
            simp only [literals, selected, pure, Pure.pure, Except.pure] at success
            apply selected_suffix formation operandProperties.2.1
              (by intro argument member; cases List.mem_singleton.mp member; exact operandProperties.2.2)
              expectedOperand expectedFormed (functionsNamed_success_subset_catalog functionsRun)
              selected (Except.ok.inj success) continuation captures
            intro extension capture
            have prior := earlier extension capture
            exact ⟨by intro argument member; cases List.mem_singleton.mp member; exact prior.1, prior.2⟩

theorem inferExprFuel_binary_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {context : SourceInference.Context} {fuel : Nat} {expression left right : Syntax.Expr}
    {operator : Syntax.Located Syntax.BinaryOp} {expected : Option Ty} {initial : State}
    (form : expression.value = .binary left operator right)
    (leftIH : InferExprFuelFormation semantic outer fuel context left none initial.allocateExpressionId.2)
    (rightIH : ∀ state, InferExprFuelFormation semantic outer fuel context right none state) :
    InferExprFuelFormation semantic outer (fuel+1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
  let id := initial.allocateExpressionId.1
  let allocated := initial.allocateExpressionId.2
  have allocationEq : initial.allocateExpressionId = (id, allocated) := rfl
  have allocation := expression_allocation_normalized allocationEq ready nodes formed
  unfold inferExprFuel at success
  simp only [allocationEq, form, bind, Except.bind] at success
  cases leftRun : inferExprFuel fuel context left none allocated with
  | error error => simp [leftRun] at success
  | ok pair =>
    rcases pair with ⟨leftValue, leftState⟩
    simp only [leftRun] at success
    have leftProperties := inferExprFuel_inferenceProperties allocation.1
      formation.validated formation.functionShapes (by simp) leftRun
    have leftNodes := (inferExprFuel_occurrenceBoundExtends leftRun).nodesBelowNextOccurrence allocation.2.1
    cases rightRun : inferExprFuel fuel context right none leftState with
    | error error => simp [rightRun] at success
    | ok pair =>
      rcases pair with ⟨rightValue, rightState⟩
      simp only [rightRun] at success
      have rightProperties := inferExprFuel_inferenceProperties leftProperties.2.1
        formation.validated formation.functionShapes (by simp) rightRun
      have expectedRight : ∀ type ∈ expected, type.VariablesBelow rightState.inference.next :=
        fun type member => (expectedBelow type member).weaken (leftProperties.1.trans rightProperties.1).next_le
      have argumentsBelow : ∀ argument ∈ [leftValue, rightValue], argument.type.VariablesBelow rightState.inference.next := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | tail
        · exact leftProperties.2.2.weaken rightProperties.1.next_le
        · cases List.mem_singleton.mp tail
          exact rightProperties.2.2
      let literals := relevantIntegerLiterals rightState allocated.integerLiterals.length [leftValue, rightValue]
      have earlier
          (rightContinuation : outer.SemanticallyExtends rightState.inference.substitution)
          (rightCapture : NoCaptureNodes outer rightState.nodes) :
          (∀ argument ∈ [leftValue, rightValue], TypeAdmissible semantic (outer.apply argument.type)) ∧
            NormalizedStateFormation semantic outer rightState := by
        have leftCapture : NoCaptureNodes outer leftState.nodes :=
          rightCapture.of_prefix (inferExprFuel_preserves_nodesPrefix
            (result := (rightValue, rightState)) rightRun (List.prefix_refl _) leftNodes (Nat.le_refl _))
        have leftFormation := leftIH allocation.1 allocation.2.1 allocation.2.2.1 formation
          (by simp) (by simp) _ leftRun (rightContinuation.trans rightProperties.1.substitution_extends) leftCapture
        have rightFormation := rightIH leftState leftProperties.2.1 leftNodes leftFormation.2 formation
          (by simp) (by simp) _ rightRun rightContinuation rightCapture
        refine ⟨?_, rightFormation.2⟩
        intro argument member
        rcases List.mem_cons.mp member with rfl | tail
        · exact leftFormation.1
        · cases List.mem_singleton.mp tail
          exact rightFormation.1
      have finish (inferred : OperatorInferenceResult)
          (operatorRun : inferBinaryOperator context operator.value leftValue.type rightValue.type expected literals rightState = .ok inferred)
          (recordRun : recordExpressionWithExpected context expression id inferred.type
            (.binary leftValue.id operator.value rightValue.id) inferred.requirements expected inferred.state = .ok result) :
          TypeAdmissible semantic (outer.apply result.1.type) ∧
            NormalizedStateFormation semantic outer result.2 := by
        have properties := inferBinaryOperator_inferenceProperties rightProperties.2.1
          (argumentsBelow leftValue (by simp)) rightProperties.2.2 expectedRight operatorRun
        have recordProperties := recordExpressionWithExpected_inferenceProperties properties.2.1 properties.2.2
          (fun type member => (expectedRight type member).weaken properties.1.next_le) recordRun
        have operatorContinuation := continuation.trans recordProperties.1.substitution_extends
        have rightCapture : NoCaptureNodes outer rightState.nodes := by
          have captured := captures.before_recordExpressionWithExpected recordRun
          rwa [(inferBinaryOperator_occurrenceState_eq operatorRun).1] at captured
        have prior := earlier (operatorContinuation.trans properties.1.substitution_extends) rightCapture
        have produced := inferBinaryOperator_normalized_formation formation prior.2
          (prior.1 leftValue (by simp)) operatorContinuation operatorRun
        exact recordExpressionWithExpected_normalized_state formation produced.2 continuation produced.1 expectedFormed recordRun
      cases dispatch : binaryOperatorDispatch operator.value with
      | traitMethod traitName methodName =>
        simp only [dispatch] at success
        cases operatorRun : inferBinaryOperator context operator.value leftValue.type rightValue.type expected literals rightState with
        | error error => simp [literals, operatorRun] at success
        | ok inferred =>
          simp only [literals, operatorRun] at success
          exact finish inferred operatorRun success
      | function name =>
        simp only [dispatch] at success
        cases functionsRun : functionsNamed context name with
        | error error => simp [functionsRun] at success
        | ok candidates =>
          simp only [functionsRun] at success
          cases candidates with
          | nil =>
            cases operatorRun : inferBinaryOperator context operator.value leftValue.type rightValue.type expected literals rightState with
            | error error => simp [literals, operatorRun] at success
            | ok inferred =>
              simp only [literals, operatorRun] at success
              exact finish inferred operatorRun success
          | cons candidate rest =>
            cases selected : selectFunctionCandidateFrom context name (candidate :: rest)
                [leftValue, rightValue] literals id (some .bool) rightState with
            | error error => simp [literals, selected] at success
            | ok attempt =>
              simp only [literals, selected] at success
              have cataloged := functionsNamed_success_subset_catalog functionsRun
              have boolBelow : ∀ type ∈ some Ty.bool, type.VariablesBelow rightState.inference.next := by
                intro type member
                cases Option.mem_def.mp member
                exact Ty.variablesBelow_constructor _ _
              have boolFormed : ∀ type ∈ some Ty.bool, TypeAdmissible semantic (outer.apply type) := by
                intro type member
                cases Option.mem_def.mp member
                exact .bool formation.scope.binders
              have selectedProperties := selectFunctionCandidateFrom_inferenceProperties
                rightProperties.2.1 argumentsBelow
                (fun signature member => formation.validated.function_scheme_body_variablesBelow
                  (cataloged member) (formation.functionShapes signature (cataloged member)) _)
                boolBelow selected
              cases fittedRun : withExpected context attempt.state attempt.result expected with
              | error error => simp [fittedRun] at success
              | ok fitted =>
                simp only [fittedRun, pure, Pure.pure, Except.pure] at success
                let callee : Syntax.Expr := {
                  span := operator.span
                  value := .identifier {span := operator.span, value := name} }
                have recordEq : recordSelectedCallResult expression callee name [leftValue, rightValue]
                    attempt fitted.expression fitted.coercions fitted.state = result := Except.ok.inj success
                have fields := recordSelectedCallResult_normalized_fields expression callee name
                  [leftValue, rightValue] attempt fitted.expression fitted.coercions fitted.state
                rw [recordEq] at fields
                have fittedContinuation : outer.SemanticallyExtends fitted.state.inference.substitution := by
                  rwa [fields.1] at continuation
                have fittedProperties := withExpected_inferenceProperties selectedProperties.2.1
                  selectedProperties.2.2
                  (fun type member => (expectedRight type member).weaken selectedProperties.1.next_le) fittedRun
                have selectedContinuation := fittedContinuation.trans fittedProperties.1.substitution_extends
                have rightCapture : NoCaptureNodes outer rightState.nodes := by
                  unfold NoCaptureNodes at captures ⊢
                  rw [fields.2.2.2.2, (withExpected_occurrenceState_eq fittedRun).1,
                    (selectFunctionCandidateFrom_occurrenceState_eq selected).1] at captures
                  exact captures
                have prior := earlier (selectedContinuation.trans selectedProperties.1.substitution_extends) rightCapture
                have selectedFormation := selectFunctionCandidateFrom_normalized_formation formation prior.2 cataloged
                  rightProperties.2.1 argumentsBelow boolBelow prior.1 boolFormed selectedContinuation selected
                have fittedFormation := withExpected_normalized_formation formation.toFormationContext
                  fittedContinuation selectedFormation.1 expectedFormed fittedRun
                have fittedStateFormed := selectedFormation.2.of_new_rows
                  (congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope fittedRun)) fittedFormation.2
                exact ⟨fields.2.2.2.1 ▸ fittedFormation.1, fittedStateFormed.congr fields.2.1 fields.2.2.1⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedInference
/-! Final normalized formation through the actual recursive source inference.
The final substitution and capture checks come from the eventual real finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceRequirementFormation

private theorem expression_state_from_rows
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {before : State} {result : InferredExpression × State}
    (initial : NormalizedStateFormation semantic outer before)
    (accepted : inferExprFuel fuel context source expected before = .ok result)
    (issued : ∀ row ∈ result.2.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    NormalizedStateFormation semantic outer result.2 :=
  initial.of_new_rows (congrArg LexicalScope.binders
    (inferExprFuel_success_lexicalScope_eq accepted)) issued

set_option maxHeartbeats 2000000 in
private theorem inferFuel_formation_internal (semantic : SourceSemantics.Context) (outer : Substitution) :
    (∀ fuel context expression expected state,
      InferExprFuelFormation semantic outer fuel context expression expected state) ∧
    (∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFormation semantic outer fuel context source id
        instantiation arguments expected state) ∧
    (∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFormation semantic outer fuel context sources
        expected state) ∧
    (∀ fuel context statements expectedReturn state,
      InferStatementsFuelFormation semantic outer fuel context statements
        expectedReturn state) ∧
    (∀ fuel context statement expectedReturn state,
      InferStatementFuelFormation semantic outer fuel context statement
        expectedReturn state) ∧
    (∀ fuel context items state,
      InferForItemsFuelFormation semantic outer fuel context items state) ∧
    (∀ fuel context item state,
      InferForItemFuelFormation semantic outer fuel context item state) ∧
    (∀ fuel context target state,
      InferPlaceFuelFormation semantic outer fuel context target state) ∧
    (∀ fuel context target operator value state,
      InferAssignedValueFuelFormation semantic outer fuel context target operator
        value state) ∧
    (∀ fuel context expressions state,
      InferExprsFuelFormation semantic outer fuel context expressions state) ∧
    (∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFormation semantic outer fuel context scrutineeType
        expectedReturn outerScope cases state) := by
  apply inferExprFuel.mutual_induct
    (motive1 := InferExprFuelFormation semantic outer)
    (motive2 := InferConstructorApplicationFuelFormation semantic outer)
    (motive3 := InferConstructorArgumentsFuelFormation semantic outer)
    (motive4 := InferStatementsFuelFormation semantic outer)
    (motive5 := InferStatementFuelFormation semantic outer)
    (motive6 := InferForItemsFuelFormation semantic outer)
    (motive7 := InferForItemFuelFormation semantic outer)
    (motive8 := InferPlaceFuelFormation semantic outer)
    (motive9 := InferAssignedValueFuelFormation semantic outer)
    (motive10 := InferExprsFuelFormation semantic outer)
    (motive11 := InferMatchCasesFuelFormation semantic outer)
  case case1 =>
    simp [InferExprFuelFormation, inferExprFuel]
  case case3 =>
    simp_all [InferExprFuelFormation, inferExprFuel, bind,
      Except.bind]
  case case5 =>
    simp_all [InferExprFuelFormation, inferExprFuel, bind,
      Except.bind]
  case case6 =>
    simp_all [InferExprFuelFormation, inferExprFuel]

  case case21 =>
    simp_all [InferExprFuelFormation, inferExprFuel]
  case case22 =>
    simp_all [InferExprFuelFormation, inferExprFuel]
  case case24 =>
    simp_all [InferConstructorApplicationFuelFormation,
      inferConstructorApplicationFuel, bind, Except.bind]
  case case27 =>
    simp_all [InferConstructorArgumentsFuelFormation,
      inferConstructorArgumentsFuel]
  case case28 =>
    simp [InferStatementsFuelFormation, inferStatementsFuel]
  case case31 =>
    simp [InferStatementFuelFormation, inferStatementFuel]
  case case32 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel,
      bind, Except.bind]
  case case47 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case48 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case50 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case52 =>
    simp_all [InferStatementFuelFormation, inferStatementFuel]
  case case55 =>
    simp [InferForItemFuelFormation, inferForItemFuel]
  case case56 =>
    simp_all [InferForItemFuelFormation, inferForItemFuel, bind,
      Except.bind]
  case case63 =>
    simp [InferPlaceFuelFormation, inferPlaceFuel]
  case case65 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case66 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case69 =>
    simp_all [InferPlaceFuelFormation, inferPlaceFuel]
  case case71 =>
    simp [InferExprsFuelFormation, inferExprsFuel]
  case case74 =>
    simp [InferMatchCasesFuelFormation, inferMatchCasesFuel]
  case case2 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_numeric_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq literalEq numericEq allocationEq expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case4 =>
    intros context expression expected initial fuel id allocated allocationEq
      literal expressionEq spelling literalEq rawValue numericEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_numeric_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq literalEq numericEq allocationEq expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case7 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq binder lookupEq localSchemeInstantiationStart
      instantiated inference advanced predicates requirements recorded requirementsEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    exact inferExprFuel_local_normalized_state formation ready formed expressionEq allocationEq
      lookupEq expectedBelow expectedFormed success continuation
  case case8 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone isBoolean
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have produced := inferExprFuel_boolean_normalized_formation formation.toFormationContext
      formation.scope.binders expressionEq allocationEq lookupNone isBoolean expectedFormed continuation success
    exact ⟨produced.1, expression_state_from_rows formed success produced.2⟩
  case case9 =>
    intros context expression expected initial fuel id allocated allocationEq
      name expressionEq lookupNone notBool
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have original := success
    have notBoolean : (name.value == "true" || name.value == "false") = false := by simpa using notBool
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupNone, notBool, bind, Except.bind] at success
    cases functionsResult : functionsNamed context name.value with
    | error error => simp [functionsResult] at success
    | ok candidates =>
      simp only [functionsResult] at success
      cases candidates with
      | nil =>
        cases builtinResult : builtinFunctionNamed? name.value with
        | none => simp [builtinResult] at success
        | some function =>
          have produced := inferExprFuel_builtin_normalized_formation formation.toFormationContext
            formation.scope.binders expressionEq allocationEq lookupNone notBoolean functionsResult builtinResult
            expectedFormed continuation original
          exact ⟨produced.1, expression_state_from_rows formed original produced.2⟩
      | cons signature rest =>
        cases rest with
        | nil =>
          have produced := inferExprFuel_declaration_normalized_formation formation.toFormationContext
            formation.scope.binders expressionEq allocationEq lookupNone notBoolean functionsResult
            expectedFormed continuation original
          exact ⟨produced.1, expression_state_from_rows formed original produced.2⟩
        | cons second tail => simp at success
  case case25 =>
    intros fuel context initial
    unfold InferConstructorArgumentsFuelFormation
    intro ready nodes formed formation below expected result success continuation captures
    simp only [inferConstructorArgumentsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at success
    subst result
    exact ⟨by simp, formed⟩
  case case29 =>
    intros context expectedReturn initial fuel
    unfold InferStatementsFuelFormation
    intro ready nodes formed formation below expected result success continuation captures
    simp only [inferStatementsFuel, Except.ok.injEq] at success
    subst result
    exact ⟨.unit formation.scope.binders, formed⟩
  case case53 =>
    intros fuel context initial
    unfold InferForItemsFuelFormation
    intro ready nodes formed formation  result success continuation captures items
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at success
    subst result
    exact formed
  case case72 =>
    intros context initial fuel
    unfold InferExprsFuelFormation
    intro ready nodes formed formation  result success continuation captures
    simp only [inferExprsFuel, Except.ok.injEq] at success
    subst result
    exact ⟨by simp, formed⟩
  case case75 =>
    intros context scrutineeType expectedReturn outerScope initial fuel
    unfold InferMatchCasesFuelFormation
    intro ready nodes formed formation scrutineeBelow scrutineeFormed returnBelow returnFormed scopeEq result success continuation captures
    simp only [inferMatchCasesFuel, Except.ok.injEq] at success
    subst result
    exact formed
  case case23 =>
    intros fuel context source id instantiation arguments expected initial arityEq argumentsInduction
    exact inferConstructorApplicationFuel_formation argumentsInduction
  case case26 =>
    intros fuel context source sources expected expectedTypes initial sourceIH tailIH
    exact inferConstructorArgumentsFuel_cons_formation sourceIH tailIH
  case case58 =>
    intros context item initial fuel name initializer itemEq initializerInduction
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none initial with
    | error error => simp [initializerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, initializerState⟩
      simp only [initializerResult, pure, Pure.pure, Except.pure] at success
      let receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result :=
        ⟨name, initializer, none, none, .none, itemEq, inferred, initializerState,
          initializerResult, (Except.ok.inj success).symm⟩
      exact initialized_header_receipt_normalized receipt initializerInduction
        ready nodes formed formation continuation captures headerCaptures
  case case59 =>
    intros context item initial fuel name sourceType initializer itemEq initializerInduction
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok resolvedType =>
      simp only [resolution] at success
      cases initializerResult : inferExprFuel fuel context initializer (some resolvedType) initial with
      | error error => simp [initializerResult] at success
      | ok pair =>
        rcases pair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        let receipt : LocalHeaderRequirementTiming.Receipt fuel context item initial result :=
          ⟨name, initializer, some sourceType, some resolvedType, .some resolution,
            itemEq, inferred, initializerState, initializerResult, (Except.ok.inj success).symm⟩
        exact initialized_header_receipt_normalized receipt (initializerInduction resolvedType)
          ready nodes formed formation continuation captures headerCaptures
  case case34 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      name initializer statementEq initializerInduction
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocatedEq : allocated = initial.allocateStatementId.2 :=
      (congrArg Prod.snd allocationEq).symm
    have cutoffEq : allocated.nextRequirement = initial.nextRequirement := by
      rw [allocatedEq]
      rfl
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases initializerResult : inferExprFuel fuel context initializer none allocated with
    | error error => simp [initializerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, initializerState⟩
      simp only [initializerResult, pure, Pure.pure, Except.pure] at success
      let receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result := {
        name, initializer, annotation := none, expected := none, annotationAccepted := .none
        form := statementEq, value := inferred, ready := initializerState
        child := by simpa only [allocationEq] using initializerResult
        completed := by simpa only [LocalLetRequirementTiming.finish, allocationEq, cutoffEq, State.withLocals] using (Except.ok.inj success).symm }
      exact initialized_statement_receipt_normalized receipt
        (by simpa only [allocationEq] using initializerInduction)
        ready nodes formed formation continuation captures
  case case35 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      name sourceType initializer statementEq initializerInduction
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocatedEq : allocated = initial.allocateStatementId.2 :=
      (congrArg Prod.snd allocationEq).symm
    have cutoffEq : allocated.nextRequirement = initial.nextRequirement := by
      rw [allocatedEq]
      rfl
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok resolvedType =>
      simp only [resolution] at success
      cases initializerResult : inferExprFuel fuel context initializer (some resolvedType) allocated with
      | error error => simp [initializerResult] at success
      | ok pair =>
        rcases pair with ⟨inferred, initializerState⟩
        simp only [initializerResult, pure, Pure.pure, Except.pure] at success
        let receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result := {
          name, initializer, annotation := some sourceType, expected := some resolvedType
          annotationAccepted := .some resolution
          form := statementEq, value := inferred, ready := initializerState
          child := by simpa only [allocationEq] using initializerResult
          completed := by simpa only [LocalLetRequirementTiming.finish, allocationEq, cutoffEq, State.withLocals] using (Except.ok.inj success).symm }
        exact initialized_statement_receipt_normalized receipt
          (by simpa only [allocationEq] using initializerInduction resolvedType)
          ready nodes formed formation continuation captures
  case case10 =>
    intros context expression expected initial fuel id allocated allocationEq
      inner expressionEq innerInduction
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases innerResult : inferExprFuel fuel context inner expected allocated with
    | error error => simp [innerResult] at success
    | ok pair =>
      rcases pair with ⟨inferred, innerState⟩
      simp only [innerResult] at success
      have properties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes expectedAllocated innerResult
      have expectedAfter : ∀ type ∈ expected, type.VariablesBelow innerState.inference.next :=
        fun type member => (expectedAllocated type member).weaken properties.1.next_le
      have recording := recordExpressionWithExpected_inferenceProperties properties.2.1
        properties.2.2 expectedAfter success
      have innerContinuation := continuation.trans recording.1.substitution_extends
      have childFormation := innerInduction allocation.1 allocation.2.1 allocation.2.2.1
        formation expectedAllocated expectedFormed _ innerResult innerContinuation
        (captures.before_recordExpressionWithExpected success)
      exact recordExpressionWithExpected_normalized_state formation childFormation.2 continuation
        childFormation.1 expectedFormed success
  case case11 =>
    intros context expression expected initial fuel id allocated allocationEq
      elements expressionEq elementsInduction
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases elementsResult : inferExprsFuel fuel context elements.elements allocated with
    | error error => simp [elementsResult] at success
    | ok pair =>
      rcases pair with ⟨inferredElements, elementsState⟩
      simp only [elementsResult] at success
      have properties := inferExprsFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes elementsResult
      have tupleBelow : (Ty.productMany (inferredElements.map (·.type))).VariablesBelow
          elementsState.inference.next := Ty.variablesBelow_productMany (by
        intro type member
        obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
        exact properties.2.2 element present)
      have expectedAfter : ∀ type ∈ expected, type.VariablesBelow elementsState.inference.next :=
        fun type member => (expectedAllocated type member).weaken properties.1.next_le
      have recording := recordExpressionWithExpected_inferenceProperties properties.2.1
        tupleBelow expectedAfter success
      have childFormation := elementsInduction allocation.1 allocation.2.1 allocation.2.2.1 formation
        _ elementsResult (continuation.trans recording.1.substitution_extends)
        (captures.before_recordExpressionWithExpected success)
      have tupleFormed : TypeAdmissible semantic (outer.apply (Ty.productMany (inferredElements.map (·.type)))) := by
        apply normalized_productMany formation.scope.binders
        intro type member
        obtain ⟨element, present, rfl⟩ := List.mem_map.mp member
        exact childFormation.1 element present
      exact recordExpressionWithExpected_normalized_state formation childFormation.2 continuation
        tupleFormed expectedFormed success

  case case73 =>
    intros context initial fuel expression rest expressionIH tailIH
    unfold InferExprsFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferExprsFuel at success
    cases expressionRun : inferExprFuel fuel context expression none initial with
    | error error => simp [expressionRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, bind, Except.bind] at success
      cases tailRun : inferExprsFuel fuel context rest expressionState with
      | error error => simp [tailRun] at success
      | ok pair =>
        rcases pair with ⟨tail, finalState⟩
        simp only [tailRun] at success
        cases success
        have expressionProperties := inferExprFuel_inferenceProperties ready
          formation.validated formation.functionShapes (by simp) expressionRun
        have expressionNodes := (inferExprFuel_occurrenceBoundExtends expressionRun).nodesBelowNextOccurrence nodes
        have tailProperties := inferExprsFuel_inferenceProperties expressionProperties.2.1
          formation.validated formation.functionShapes tailRun
        have expressionCaptures : NoCaptureNodes outer expressionState.nodes :=
          captures.of_prefix (inferExprsFuel_preserves_nodesPrefix (result := (tail, finalState)) tailRun
            (List.prefix_refl _) expressionNodes (Nat.le_refl _))
        have expressionFormation := expressionIH ready nodes formed formation
          (by simp) (by simp) _ expressionRun
          (continuation.trans tailProperties.1.substitution_extends) expressionCaptures
        have tailFormation := tailIH expressionState expressionProperties.2.1
          expressionNodes expressionFormation.2 formation _ tailRun continuation captures
        refine ⟨?_, tailFormation.2⟩
        intro element member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact expressionFormation.1
        · exact tailFormation.1 element tailMember
  case case30 =>
    intros context expectedReturn initial fuel statement rest statementIH tailIH
    unfold InferStatementsFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    unfold inferStatementsFuel at success
    cases headRun : inferStatementFuel fuel context statement expectedReturn initial with
    | error error => simp [headRun, bind, Except.bind] at success
    | ok head =>
      simp only [headRun, bind, Except.bind] at success
      have headProperties := inferStatementFuel_inferenceProperties ready
        formation.validated formation.functionShapes returnBelow headRun
      have headNodes := (inferStatementFuel_occurrenceBoundExtends headRun).nodesBelowNextOccurrence nodes
      cases rest with
      | nil =>
        injection success with resultEq
        subst result
        have headFormation := statementIH ready nodes formed formation returnBelow returnFormed
          head headRun continuation captures
        refine ⟨?_, headFormation.2⟩
        split
        · exact headFormation.1
        · exact .unit formation.scope.binders
      | cons next remaining =>
        cases tailRun : inferStatementsFuel fuel context (next :: remaining) expectedReturn head.state with
        | error error => simp [tailRun] at success
        | ok tail =>
          simp only [tailRun] at success
          injection success with resultEq
          subst result
          have tailProperties := inferStatementsFuel_inferenceProperties headProperties.2.1
            formation.validated formation.functionShapes
            (returnBelow.weaken headProperties.1.next_le) tailRun
          have headCaptures : NoCaptureNodes outer head.state.nodes :=
            captures.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := tail) tailRun
              (List.prefix_refl _) headNodes (Nat.le_refl _))
          have headFormation := statementIH ready nodes formed formation returnBelow returnFormed
            head headRun (continuation.trans tailProperties.1.substitution_extends) headCaptures
          have tailFormation := tailIH head headProperties.2.1 headNodes headFormation.2
            formation (returnBelow.weaken headProperties.1.next_le) returnFormed
            tail tailRun continuation captures
          refine ⟨?_, tailFormation.2⟩
          split
          · exact tailFormation.1
          · split
            · exact headFormation.1
            · exact tailFormation.1

  case case60 =>
    intros context item initial fuel expression itemEq expressionIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases expressionRun : inferExprFuel fuel context expression none initial with
    | error error => simp [expressionRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact (expressionIH ready nodes formed formation (by simp) (by simp)
        _ expressionRun continuation captures).2
  case case61 =>
    intros context item initial fuel target operator value itemEq assignmentIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases assignmentRun : inferAssignedValueFuel fuel context target operator.value value initial with
    | error error => simp [assignmentRun] at success
    | ok triple =>
      rcases triple with ⟨assignment, inferred, assignmentState⟩
      simp only [assignmentRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact (assignmentIH ready nodes formed formation _ assignmentRun continuation captures).2.2
  case case67 =>
    intros context target initial fuel inner targetEq innerIH
    unfold InferPlaceFuelFormation at *
    intro ready nodes formed formation result success continuation captures
    exact innerIH ready nodes formed formation result
      (by simpa only [inferPlaceFuel, targetEq] using success) continuation captures
  case case64 =>
    intros context target initial fuel name targetEq binder lookupEq monomorphic
    unfold InferPlaceFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferPlaceFuel at success
    simp only [targetEq, lookupEq, monomorphic, if_true] at success
    injection success with resultEq
    subst result
    have binderFormed := formed.binders binder (State.lookupBinder?_eq_some_facts lookupEq).1
    exact ⟨(continuation binder.scheme.body).symm ▸ binderFormed.body, formed⟩

  case case37 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      value statementEq valueIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases valueRun : inferExprFuel fuel context value (some expectedReturn) allocated with
    | error error => simp [valueRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, valueState⟩
      simp only [valueRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have valueFormation := valueIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        (by simpa using returnAllocated) (by simpa using returnFormed)
        _ valueRun continuation captures.before_recordNode
      exact ⟨(continuation expectedReturn).symm ▸ returnFormed, valueFormation.2.recordNode _⟩
  case case38 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      expression trailingSemicolon statementEq expressionIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases expressionRun : inferExprFuel fuel context expression none allocated with
    | error error => simp [expressionRun] at success
    | ok pair =>
      rcases pair with ⟨inferred, expressionState⟩
      simp only [expressionRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have expressionFormation := expressionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        (by simp) (by simp) _ expressionRun continuation captures.before_recordNode
      refine ⟨?_, expressionFormation.2.recordNode _⟩
      split
      · exact .unit formation.scope.binders
      · exact expressionFormation.1
  case case41 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      target operator value statementEq assignmentIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases assignmentRun : inferAssignedValueFuel fuel context target operator.value value allocated with
    | error error => simp [assignmentRun] at success
    | ok triple =>
      rcases triple with ⟨assignment, inferred, assignmentState⟩
      simp only [assignmentRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have assignmentFormation := assignmentIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        _ assignmentRun continuation captures.before_recordNode
      exact ⟨.unit formation.scope.binders, assignmentFormation.2.2.recordNode _⟩
  case case40 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq body statementEq bodyIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases bodyRun : inferStatementsFuel fuel context body expectedReturn allocated with
    | error error => simp [bodyRun] at success
    | ok bodyResult =>
      simp only [bodyRun, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      have bodyFormation := bodyIH allocation.1 allocation.2.1 allocation.2.2.1 formation
        returnAllocated returnFormed _ bodyRun continuation captures.before_recordNode
      exact ⟨bodyFormation.1,
        (allocation.2.2.1.restore bodyFormation.2 allocated.lexicalScope (fun _ member => member)).recordNode _⟩
  case case36 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases unified : Detail.unify allocated .unit expectedReturn with
    | error error => simp [unified] at success
    | ok unifiedState =>
      simp only [unified, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact ⟨(continuation expectedReturn).symm ▸ returnFormed,
        (allocation.2.2.1.unify unified).recordNode _⟩

  case case49 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq loopNonzero
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨.unit formation.scope.binders, allocation.2.2.1.recordNode _⟩
  case case51 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq statementEq loopNonzero
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, loopNonzero, if_false] at success
    injection success with resultEq
    subst result
    exact ⟨.unit formation.scope.binders, allocation.2.2.1.recordNode _⟩
  case case33 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq name sourceType statementEq
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok type =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact ⟨.unit formation.scope.binders,
        (uninitialized_binding_normalized name formation allocation.2.2.1 resolution continuation).recordNode _⟩
  case case57 =>
    intros context item initial fuel name sourceType itemEq
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok type =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      subst result
      exact uninitialized_binding_normalized name formation formed resolution continuation
  case case54 =>
    intros fuel context item items initial itemIH tailIH
    unfold InferForItemsFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemsFuel at success
    cases itemRun : inferForItemFuel fuel context item initial with
    | error error => simp [itemRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨inferred, itemState⟩
      simp only [itemRun, bind, Except.bind] at success
      cases tailRun : inferForItemsFuel fuel context items itemState with
      | error error => simp [tailRun] at success
      | ok tail =>
        simp only [tailRun] at success
        cases success
        have itemProperties := inferForItemFuel_inferenceProperties ready
          formation.validated formation.functionShapes itemRun
        have itemNodes := (inferForItemFuel_occurrenceBoundExtends itemRun).nodesBelowNextOccurrence nodes
        have tailProperties := inferForItemsFuel_inferenceProperties itemProperties.2
          formation.validated formation.functionShapes tailRun
        have itemCaptures : NoCaptureNodes outer itemState.nodes :=
          captures.of_prefix (inferForItemsFuel_preserves_nodesPrefix (result := tail) tailRun
            (List.prefix_refl _) itemNodes (Nat.le_refl _))
        have oneCapture : NoCaptureItems outer [inferred] := by
          intro binder member
          apply headerCaptures binder
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
            (List.mem_append_left (tail.items.flatMap ForItemForm.initializedLetBinders) member)
        have restCapture : NoCaptureItems outer tail.items := by
          intro binder member
          exact headerCaptures binder (List.mem_append_right _ member)
        have itemFormation := itemIH ready nodes formed formation _ itemRun
          (continuation.trans tailProperties.1.substitution_extends) itemCaptures oneCapture
        exact tailIH itemState itemProperties.2 itemNodes itemFormation formation
          tail tailRun continuation captures restCapture

  case case18 =>
    intros context expression expected initial fuel id allocated allocationEq marker sourceType expressionEq
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases resolution : resolveSourceType context sourceType with
    | error error => simp [resolution] at success
    | ok inner =>
      simp only [resolution] at success
      have innerFormed : TypeAdmissible semantic (outer.apply inner) :=
        (annotation_normalized_formation formation (.some resolution) 0).2 _ (by simp)
      have proxyFormed : TypeAdmissible semantic (outer.apply (.proxy inner)) :=
        .proxy innerFormed
      exact recordExpressionWithExpected_normalized_state formation allocation.2.2.1
        continuation proxyFormed expectedFormed success

  case case15 =>
    intros context expression expected initial fuel id allocated allocationEq
      keyword parameters returnType body expressionEq bodyIH
    exact inferExprFuel_lambda_formation expressionEq bodyIH

  case case62 =>
    intros context item initial fuel target operator itemEq placeIH
    unfold InferForItemFuelFormation
    intro ready nodes formed formation result success continuation captures headerCaptures
    unfold inferForItemFuel at success
    simp only [itemEq, bind, Except.bind] at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun] at success
      cases unified : Detail.unify placeState place.type .word with
      | error error => simp [unified] at success
      | ok unifiedState =>
        simp only [unified, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        subst result
        have placeProperties := inferPlaceFuel_inferenceProperties ready
          formation.validated formation.functionShapes placeRun
        have progress := unify_inferenceProgress placeProperties.2.1.solved
          placeProperties.2.2 (Ty.variablesBelow_constructor _ _) unified
        have placeFormation := placeIH ready nodes formed formation _ placeRun
          (continuation.trans progress.substitution_extends) (captures.before_unify unified)
        exact placeFormation.2.unify unified
  case case42 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      target operator statementEq placeIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases placeRun : inferPlaceFuel fuel context target allocated with
    | error error => simp [placeRun] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun] at success
      cases unified : Detail.unify placeState place.type .word with
      | error error => simp [unified] at success
      | ok unifiedState =>
        simp only [unified, pure, Pure.pure, Except.pure] at success
        injection success with resultEq
        subst result
        have placeProperties := inferPlaceFuel_inferenceProperties allocation.1
          formation.validated formation.functionShapes placeRun
        have progress := unify_inferenceProgress placeProperties.2.1.solved
          placeProperties.2.2 (Ty.variablesBelow_constructor _ _) unified
        have placeFormation := placeIH allocation.1 allocation.2.1 allocation.2.2.1 formation _ placeRun
          (continuation.trans progress.substitution_extends)
          (captures.before_recordNode.before_unify unified)
        exact ⟨.unit formation.scope.binders, (placeFormation.2.unify unified).recordNode _⟩
  case case46 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      condition body statementEq conditionIH bodyIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    let loopContext := {context with loopDepth := context.loopDepth + 1}
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨inferredCondition, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have returnCondition : expectedReturn.VariablesBelow conditionState.inference.next := by
        apply Ty.VariablesBelow.weaken _ conditionProperties.1.next_le
        simpa only [allocation.2.2.2] using returnBelow
      cases bodyRun : inferStatementsFuel fuel loopContext body.value expectedReturn conditionState with
      | error error => simp [loopContext, bodyRun] at success
      | ok bodyResult =>
        simp only [loopContext, bodyRun] at success
        injection success with resultEq
        subst result
        have bodyProperties := inferStatementsFuel_inferenceProperties (context := loopContext) conditionProperties.2.1
          formation.validated formation.functionShapes returnCondition bodyRun
        have bodyCapture : NoCaptureNodes outer bodyResult.state.nodes := captures.before_recordNode
        have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
          bodyCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := bodyResult) bodyRun
            (List.prefix_refl _) conditionNodes (Nat.le_refl _))
        have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
          (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
          (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
          _ conditionRun (continuation.trans bodyProperties.1.substitution_extends) conditionCapture
        have bodyFormation := bodyIH conditionState conditionProperties.2.1 conditionNodes conditionFormation.2
          (formation.withLoopDepth _) returnCondition returnFormed _ bodyRun continuation bodyCapture
        exact ⟨.unit formation.scope.binders,
          (conditionFormation.2.restore bodyFormation.2 conditionState.lexicalScope (fun _ member => member)).recordNode _⟩

  case case70 =>
    intros fuel context target operator value initial placeIH valueIH
    unfold InferAssignedValueFuelFormation
    intro ready nodes formed formation result success continuation captures
    unfold inferAssignedValueFuel at success
    cases placeRun : inferPlaceFuel fuel context target initial with
    | error error => simp [placeRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨place, placeState⟩
      simp only [placeRun, bind, Except.bind] at success
      have placeProperties := inferPlaceFuel_inferenceProperties ready
        formation.validated formation.functionShapes placeRun
      have placeNodes := (inferPlaceFuel_occurrenceBoundExtends placeRun).nodesBelowNextOccurrence nodes
      have finishValue (fitted : State)
          (progress : placeState.InferenceProgress fitted)
          (fitReady : fitted.InferenceReady) (fitNodes : fitted.NodesBelowNextOccurrence)
          (sameNodes : fitted.nodes = placeState.nodes)
          (sameBinders : fitted.localBinders = placeState.localBinders)
          (sameRows : fitted.requirements = placeState.requirements)
          (expected : Ty) (expectedBelow : expected.VariablesBelow fitted.inference.next)
          (expectedFormed : outer.SemanticallyExtends fitted.inference.substitution →
            TypeAdmissible semantic (outer.apply place.type) →
            TypeAdmissible semantic (outer.apply expected))
          (child : InferExprFuelFormation semantic outer fuel context value (some expected) fitted)
          (accepted : (do
            let (inferred, finalState) ← inferExprFuel fuel context value (some expected) fitted
            pure (({target := {place with type := finalState.resolve place.type}} : AssignmentResolution), inferred, finalState)) = .ok result) :
          TypeAdmissible semantic (outer.apply result.1.target.type) ∧
            TypeAdmissible semantic (outer.apply result.2.1.type) ∧
            NormalizedStateFormation semantic outer result.2.2 := by
        cases valueRun : inferExprFuel fuel context value (some expected) fitted with
        | error error => simp [valueRun, bind, Except.bind] at accepted
        | ok pair =>
          rcases pair with ⟨inferred, finalState⟩
          simp only [valueRun, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          have valueProperties := inferExprFuel_inferenceProperties fitReady
            formation.validated formation.functionShapes (by simpa using expectedBelow) valueRun
          have fitContinuation := continuation.trans valueProperties.1.substitution_extends
          have fitCapture : NoCaptureNodes outer fitted.nodes :=
            captures.of_prefix (inferExprFuel_preserves_nodesPrefix (result := (inferred, finalState)) valueRun
              (List.prefix_refl _) fitNodes (Nat.le_refl _))
          have placeCapture : NoCaptureNodes outer placeState.nodes := sameNodes ▸ fitCapture
          have placeFormation := placeIH ready nodes formed formation _ placeRun
            (fitContinuation.trans progress.substitution_extends) placeCapture
          have valueFormation := child fitReady fitNodes
            (placeFormation.2.congr sameBinders sameRows) formation
            (by simpa using expectedBelow) (by simpa using expectedFormed fitContinuation placeFormation.1)
            _ valueRun continuation captures
          exact ⟨(continuation place.type).symm ▸ placeFormation.1, valueFormation⟩
      have finishNonEqual
          (child : ∀ fitted, InferExprFuelFormation semantic outer fuel context value (some .word) fitted)
          (accepted : (do
            let fitted ← Detail.unify placeState place.type .word
            let (inferred, finalState) ← inferExprFuel fuel context value (some .word) fitted
            pure (({target := {place with type := finalState.resolve place.type}} : AssignmentResolution), inferred, finalState)) = .ok result) :
          TypeAdmissible semantic (outer.apply result.1.target.type) ∧
            TypeAdmissible semantic (outer.apply result.2.1.type) ∧
            NormalizedStateFormation semantic outer result.2.2 := by
        cases fitRun : Detail.unify placeState place.type .word with
        | error error => simp [fitRun, bind, Except.bind] at accepted
        | ok fitted =>
          simp only [fitRun, bind, Except.bind] at accepted
          have progress := unify_inferenceProgress placeProperties.2.1.solved
            placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fitRun
          have fitReady := unify_preserves_inferenceReady placeProperties.2.1
            placeProperties.2.2 (Ty.variablesBelow_constructor _ _) fitRun
          have fitNodes : fitted.NodesBelowNextOccurrence := by
            intro node member
            rw [(unify_occurrenceState_eq fitRun).1] at member
            rw [(unify_occurrenceState_eq fitRun).2]
            exact placeNodes node member
          exact finishValue fitted progress fitReady fitNodes (unify_occurrenceState_eq fitRun).1
            (congrArg LexicalScope.binders (unify_preserves_lexicalScope fitRun)) (unify_requirements_eq fitRun)
            .word (Ty.variablesBelow_constructor _ _) (fun _ _ => .word formation.scope.binders)
            (child fitted) accepted
      cases operator with
      | equal =>
        simp only [pure, Pure.pure, Except.pure] at success
        exact finishValue placeState (.refl placeProperties.2.1.solved) placeProperties.2.1
          placeNodes rfl rfl rfl (placeState.resolve place.type)
          (placeProperties.2.1.solved.variablesBelow_apply placeProperties.2.2)
          (fun extension formedType => (extension place.type).symm ▸ formedType)
          (valueIH place placeState) success
      | add => exact finishNonEqual (valueIH place) success
      | subtract => exact finishNonEqual (valueIH place) success
      | multiply => exact finishNonEqual (valueIH place) success
      | divide => exact finishNonEqual (valueIH place) success
      | modulo => exact finishNonEqual (valueIH place) success
      | bitAnd => exact finishNonEqual (valueIH place) success
      | bitXor => exact finishNonEqual (valueIH place) success
      | bitOr => exact finishNonEqual (valueIH place) success
      | shiftLeft => exact finishNonEqual (valueIH place) success
      | shiftRight => exact finishNonEqual (valueIH place) success
      | uncheckedAdd => exact finishNonEqual (valueIH place) success
      | uncheckedSubtract => exact finishNonEqual (valueIH place) success
      | uncheckedMultiply => exact finishNonEqual (valueIH place) success

  case case14 =>
    intros context expression expected initial fuel id allocated allocationEq
      condition question thenBranch colon elseBranch expressionEq conditionIH thenIH elseIH
    unfold InferExprFuelFormation
    intro ready nodes formed formation expectedBelow expectedFormed result success continuation captures
    have allocation := expression_allocation_normalized allocationEq ready nodes formed
    have expectedAllocated : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using expectedBelow
    unfold inferExprFuel at success
    simp only [allocationEq, expressionEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨conditionValue, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have expectedCondition : ∀ type ∈ expected, type.VariablesBelow conditionState.inference.next :=
        fun type member => (expectedAllocated type member).weaken conditionProperties.1.next_le
      cases thenRun : inferExprFuel fuel context thenBranch expected conditionState with
      | error error => simp [thenRun] at success
      | ok pair =>
        rcases pair with ⟨thenValue, thenState⟩
        simp only [thenRun] at success
        have thenProperties := inferExprFuel_inferenceProperties conditionProperties.2.1
          formation.validated formation.functionShapes expectedCondition thenRun
        have thenNodes := (inferExprFuel_occurrenceBoundExtends thenRun).nodesBelowNextOccurrence conditionNodes
        have expectedThen : ∀ type ∈ expected, type.VariablesBelow thenState.inference.next :=
          fun type member => (expectedCondition type member).weaken thenProperties.1.next_le
        cases elseRun : inferExprFuel fuel context elseBranch expected thenState with
        | error error => simp [elseRun] at success
        | ok pair =>
          rcases pair with ⟨elseValue, elseState⟩
          simp only [elseRun] at success
          have elseProperties := inferExprFuel_inferenceProperties thenProperties.2.1
            formation.validated formation.functionShapes expectedThen elseRun
          have thenBelow := thenProperties.2.2.weaken elseProperties.1.next_le
          cases unified : Detail.unify elseState thenValue.type elseValue.type with
          | error error => simp [unified] at success
          | ok unifiedState =>
            simp only [unified] at success
            have unifyProgress := unify_inferenceProgress elseProperties.2.1.solved
              thenBelow elseProperties.2.2 unified
            have unifiedReady := unify_preserves_inferenceReady elseProperties.2.1
              thenBelow elseProperties.2.2 unified
            have expectedUnified : ∀ type ∈ expected, type.VariablesBelow unifiedState.inference.next :=
              fun type member => (expectedThen type member).weaken
                (elseProperties.1.trans unifyProgress).next_le
            have recording := recordExpressionWithExpected_inferenceProperties unifiedReady
              (unifyProgress.resolve_variablesBelow thenBelow) expectedUnified success
            have unifiedContinuation := continuation.trans recording.1.substitution_extends
            have elseContinuation := unifiedContinuation.trans unifyProgress.substitution_extends
            have thenContinuation := elseContinuation.trans elseProperties.1.substitution_extends
            have conditionContinuation := thenContinuation.trans thenProperties.1.substitution_extends
            have unifiedCapture : NoCaptureNodes outer unifiedState.nodes :=
              captures.before_recordExpressionWithExpected success
            have elseCapture := unifiedCapture.before_unify unified
            have thenCapture : NoCaptureNodes outer thenState.nodes :=
              elseCapture.of_prefix (inferExprFuel_preserves_nodesPrefix
                (result := (elseValue, elseState)) elseRun (List.prefix_refl _) thenNodes (Nat.le_refl _))
            have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
              thenCapture.of_prefix (inferExprFuel_preserves_nodesPrefix
                (result := (thenValue, thenState)) thenRun (List.prefix_refl _) conditionNodes (Nat.le_refl _))
            have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
              (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
              (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
              _ conditionRun conditionContinuation conditionCapture
            have thenFormation := thenIH conditionState conditionProperties.2.1 conditionNodes
              conditionFormation.2 formation expectedCondition expectedFormed _ thenRun thenContinuation thenCapture
            have elseFormation := elseIH thenState thenProperties.2.1 thenNodes thenFormation.2 formation
              expectedThen expectedFormed _ elseRun elseContinuation elseCapture
            exact recordExpressionWithExpected_normalized_state formation (elseFormation.2.unify unified)
              continuation ((unifiedContinuation thenValue.type).symm ▸ thenFormation.1) expectedFormed success

  case case43 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro source single casesIH bodyIH sourceIH
    apply inferStatementFuel_match_single_formation form single casesIH bodyIH
    simpa only [allocationEq] using sourceIH
  case case44 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq scrutinees arms form
    dsimp only
    intro notSingleton casesIH bodyIH sourcesIH
    apply inferStatementFuel_match_many_formation form notSingleton casesIH bodyIH
    simpa only [allocationEq] using sourcesIH
  case case76 =>
    intros context scrutineeType expectedReturn outerScope initial fuel arm rest bodyIH tailIH
    exact inferMatchCasesFuel_cons_formation bodyIH tailIH

  case case39 =>
    intros context statement expectedReturn initial fuel id allocated allocationEq
      condition thenBody elseBody statementEq conditionIH thenIH elseIH
    unfold InferStatementFuelFormation
    intro ready nodes formed formation returnBelow returnFormed result success continuation captures
    have allocation := statement_allocation_normalized allocationEq ready nodes formed
    have returnAllocated : expectedReturn.VariablesBelow allocated.inference.next := by
      simpa only [allocation.2.2.2] using returnBelow
    unfold inferStatementFuel at success
    simp only [allocationEq, statementEq, bind, Except.bind] at success
    cases conditionRun : inferExprFuel fuel context condition (some .bool) allocated with
    | error error => simp [conditionRun] at success
    | ok pair =>
      rcases pair with ⟨conditionValue, conditionState⟩
      simp only [conditionRun] at success
      have conditionProperties := inferExprFuel_inferenceProperties allocation.1
        formation.validated formation.functionShapes (by
          intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _) conditionRun
      have conditionNodes := (inferExprFuel_occurrenceBoundExtends conditionRun).nodesBelowNextOccurrence allocation.2.1
      have returnCondition := returnAllocated.weaken conditionProperties.1.next_le
      cases thenRun : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
      | error error => simp [thenRun] at success
      | ok thenResult =>
        simp only [thenRun] at success
        have thenProperties := inferStatementsFuel_inferenceProperties conditionProperties.2.1
          formation.validated formation.functionShapes returnCondition thenRun
        have thenNodes := (inferStatementsFuel_occurrenceBoundExtends thenRun).nodesBelowNextOccurrence conditionNodes
        let afterThen := thenResult.state.restoreLexicalScope conditionState.lexicalScope
        have restored : conditionState.InferenceProgress afterThen ∧ afterThen.InferenceReady :=
          State.restoreLexicalScope_inferenceProperties conditionProperties.2.1 thenProperties.1
        have prefixFormation
            (thenContinuation : outer.SemanticallyExtends thenResult.state.inference.substitution)
            (thenCapture : NoCaptureNodes outer thenResult.state.nodes) :
            NormalizedStateFormation semantic outer conditionState ∧
              NormalizedStateFormation semantic outer afterThen := by
          have conditionCapture : NoCaptureNodes outer conditionState.nodes :=
            thenCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := thenResult) thenRun
              (List.prefix_refl _) conditionNodes (Nat.le_refl _))
          have conditionFormation := conditionIH allocation.1 allocation.2.1 allocation.2.2.1 formation
            (by intro type member; cases Option.mem_def.mp member; exact Ty.variablesBelow_constructor _ _)
            (by intro type member; cases Option.mem_def.mp member; exact .bool formation.scope.binders)
            _ conditionRun (thenContinuation.trans thenProperties.1.substitution_extends) conditionCapture
          have thenFormation := thenIH conditionState conditionProperties.2.1 conditionNodes conditionFormation.2
            formation returnCondition returnFormed _ thenRun thenContinuation thenCapture
          exact ⟨conditionFormation.2,
            conditionFormation.2.restore thenFormation.2 conditionState.lexicalScope (fun _ member => member)⟩
        cases elseBody with
        | none =>
          simp only [pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          subst result
          have prior := prefixFormation continuation captures.before_recordNode
          exact ⟨.unit formation.scope.binders, prior.2.recordNode _⟩
        | some elseBody =>
          cases elseRun : inferStatementsFuel fuel context elseBody.value expectedReturn afterThen with
          | error error => simp [afterThen, elseRun] at success
          | ok elseResult =>
            simp only [afterThen, elseRun, pure, Pure.pure, Except.pure] at success
            injection success with resultEq
            subst result
            have elseProperties := inferStatementsFuel_inferenceProperties restored.2
              formation.validated formation.functionShapes (returnCondition.weaken restored.1.next_le) elseRun
            have elseCapture : NoCaptureNodes outer elseResult.state.nodes := captures.before_recordNode
            have thenCapture : NoCaptureNodes outer thenResult.state.nodes :=
              elseCapture.of_prefix (inferStatementsFuel_preserves_nodesPrefix (result := elseResult) elseRun
                (List.prefix_refl _) thenNodes (Nat.le_refl _))
            have prior := prefixFormation (continuation.trans elseProperties.1.substitution_extends) thenCapture
            have elseFormation := elseIH conditionState thenResult elseBody restored.2 thenNodes prior.2
              formation (returnCondition.weaken restored.1.next_le) returnFormed _ elseRun continuation elseCapture
            refine ⟨?_, (prior.1.restore elseFormation.2 conditionState.lexicalScope (fun _ member => member)).recordNode _⟩
            split
            · exact (continuation expectedReturn).symm ▸ returnFormed
            · exact .unit formation.scope.binders

  case case16 =>
    intro context expression expected initial fuel id allocated allocationEq callee arguments expressionEq constructorIH argumentsIH calleeIH
    apply inferExprFuel_call_formation expressionEq
    · intro instantiation state
      simpa only [allocationEq] using constructorIH instantiation state
    · simpa only [allocationEq] using argumentsIH
    · exact calleeIH
  case case17 =>
    intro context expression expected initial fuel id allocated allocationEq dot name arguments expressionEq constructorIH
    apply inferExprFuel_dotConstructor_formation expressionEq
    intro dataType constructor typeArguments
    simpa only [allocationEq] using constructorIH dataType constructor typeArguments
  case case20 =>
    intro context expression expected initial fuel id allocated allocationEq base dot name expressionEq constructorIH
    apply inferExprFuel_fieldConstructor_formation expressionEq
    intro instantiation state
    simpa only [allocationEq] using constructorIH instantiation state

  case case12 =>
    intro context expression expected initial fuel id allocated allocationEq operator operand form operandIH
    apply inferExprFuel_unary_formation form
    simpa only [allocationEq] using operandIH
  case case13 =>
    intro context expression expected initial fuel id allocated allocationEq left operator right form leftIH rightIH
    apply inferExprFuel_binary_formation form
    · simpa only [allocationEq] using leftIH
    · exact rightIH
  case case19 =>
    intro context expression expected initial fuel id allocated allocationEq base brackets index form baseIH indexIH
    apply inferExprFuel_index_formation form
    · simpa only [allocationEq] using baseIH
    · exact indexIH
  case case68 =>
    intro context target initial fuel base brackets key form baseIH keyIH
    exact inferPlaceFuel_index_formation form baseIH keyIH
  case case45 =>
    intro context statement expectedReturn initial fuel id allocated allocationEq headerSpan initializer condition post body form initializerIH conditionIH bodyIH postIH
    apply inferStatementFuel_for_formation form
    · simpa only [allocationEq] using initializerIH
    · exact conditionIH
    · exact bodyIH
    · exact postIH

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferExprFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context expression expected state,
      InferExprFuelFormation semantic outer fuel context expression expected state :=
  (inferFuel_formation_internal semantic outer).1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferConstructorApplicationFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context source id instantiation arguments expected state,
      InferConstructorApplicationFuelFormation semantic outer fuel context source id instantiation arguments expected state :=
  (inferFuel_formation_internal semantic outer).2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferConstructorArgumentsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context sources expected state,
      InferConstructorArgumentsFuelFormation semantic outer fuel context sources expected state :=
  (inferFuel_formation_internal semantic outer).2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferStatementsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context statements expectedReturn state,
      InferStatementsFuelFormation semantic outer fuel context statements expectedReturn state :=
  (inferFuel_formation_internal semantic outer).2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferStatementFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context statement expectedReturn state,
      InferStatementFuelFormation semantic outer fuel context statement expectedReturn state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferForItemsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context items state,
      InferForItemsFuelFormation semantic outer fuel context items state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferForItemFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context item state,
      InferForItemFuelFormation semantic outer fuel context item state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferPlaceFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context target state,
      InferPlaceFuelFormation semantic outer fuel context target state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferAssignedValueFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context target operator value state,
      InferAssignedValueFuelFormation semantic outer fuel context target operator value state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferExprsFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context expressions state,
      InferExprsFuelFormation semantic outer fuel context expressions state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.2.1

/-- Normalized formation follows the actual successful inference call and its recursive children. -/
theorem inferMatchCasesFuel_normalized_formation (semantic : SourceSemantics.Context) (outer : Substitution) :
    ∀ fuel context scrutineeType expectedReturn outerScope cases state,
      InferMatchCasesFuelFormation semantic outer fuel context scrutineeType expectedReturn outerScope cases state :=
  (inferFuel_formation_internal semantic outer).2.2.2.2.2.2.2.2.2.2


end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceNormalizedRequirementFormation
/-! Retained local-read issuances preserve the prior binder's normalized formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceRequirementFormation
open Frontend SourceInference TypeSystem SourceInferenceSoundness

private theorem row_eq_of_unique_ids
    {rows : List Requirement}
    (unique : (rows.map (fun row => row.id.index)).Nodup)
    {left right : Requirement} (leftMember : left ∈ rows)
    (rightMember : right ∈ rows) (same : left.id = right.id) : left = right := by
  induction rows generalizing left right with
  | nil => simp at leftMember
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨right, rightMember, congrArg RequirementId.index same.symm⟩))
      · rcases rightMember with rfl | rightMember
        · exact False.elim (unique.1 (List.mem_map.mpr
            ⟨left, leftMember, congrArg RequirementId.index same⟩))
        · exact induction unique.2 leftMember rightMember same

/-- Actual ledger identities select the producer's exact predicate before
normalization; later ledger membership alone does not supply its formation. -/
theorem retained_normalized_issued_row_formed
    {context : SourceSemantics.Context} {state : State} {outer : Substitution}
    {predicates : List ProgramPredicate} {ids : List RequirementId}
    (wellFormed : state.RequirementsWellFormed)
    (correspondence : RequirementPredicatesCorrespond state.requirements predicates ids)
    (formed : ∀ predicate ∈ predicates,
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate))
    {row : Requirement} (member : row ∈ state.requirements) (selected : row.id ∈ ids) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have origin : ∃ predicate, ({ id := row.id, predicate } : Requirement) ∈ state.requirements ∧
      PredicateAdmissible context (TypedTraitResolution.applySubstitution outer predicate) := by
    induction correspondence with
    | nil => simp at selected
    | @cons predicate id predicates ids head _ ih =>
      rcases List.mem_cons.mp selected with rfl | tail
      · exact ⟨predicate, head, formed predicate (by simp)⟩
      · exact ih (fun predicate member => formed predicate (by simp [member])) tail
  obtain ⟨predicate, issuedMember, predicateFormed⟩ := origin
  have unique : (state.requirements.map (fun row => row.id.index)).Nodup := by
    rw [show state.requirements.map (fun row => row.id.index) =
      List.range state.nextRequirement from wellFormed]
    exact List.nodup_range
  have same := row_eq_of_unique_ids unique member issuedMember rfl
  exact (congrArg Requirement.predicate same).symm ▸ predicateFormed

/-- An actual earlier lookup contributes normalized formation for the exact
retained row of its real batch, using that earlier binder's certificate. -/
theorem retained_local_read_row_formed
    (lookup : LocalReadEvents.Lookup)
    {outer : Substitution} {context : SourceSemantics.Context} {retained : State}
    (binders : TypeParameterBindersWellFormed context)
    (residual : context.residualTypeVariables = true)
    (range : SubstitutionRangeAdmissible context outer)
    (formation : LocalSchemeRequirementsWellFormed context (lookup.binder.applySubstitution outer))
    (scheme : SchemeWellFormed context (lookup.binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer lookup.binder)
    (continuation : outer.SemanticallyExtends lookup.advanced.inference.substitution)
    (included : lookup.result.2.requirements ⊆ retained.requirements)
    (wellFormed : retained.RequirementsWellFormed)
    {row : Requirement} (member : row ∈ retained.requirements)
    (selected : row.id ∈ lookup.batch.1) :
    PredicateAdmissible context (TypedTraitResolution.applySubstitution outer row.predicate) := by
  have issuance := local_read_issuance lookup binders residual range formation scheme noCapture continuation
  exact retained_normalized_issued_row_formed wellFormed (issuance.1.mono included)
    issuance.2 member selected

/-- Normalized producer formation connects directly to the existing let
certificate. Actual continuation absorbs the ready substitution and actual
no-capture removes the quantifier restriction. -/
theorem retained_formation_of_normalized_issuances
    {ready : State} {binder : TypedBinder} {outer : Substitution}
    {target : SourceSemantics.Context}
    (continuation : outer.SemanticallyExtends ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (issued : ∀ row ∈ ready.requirements, row.id ∈ localSchemeTemplateIds binder →
      PredicateAdmissible (localSchemeInitializerContext target (binder.applySubstitution outer))
        (TypedTraitResolution.applySubstitution outer row.predicate)) :
    RetainedRequirementPredicateFormationAt ready binder outer target := by
  intro row member selected
  rw [retained_predicate_normalization continuation noCapture]
  exact issued row member selected

end Solcore.SourceSemantics.SourceInferenceRequirementFormation
end
