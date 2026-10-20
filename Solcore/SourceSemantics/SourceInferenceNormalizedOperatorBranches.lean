import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorContinuation
import Solcore.SourceSemantics.SourceInferenceNormalizedCallFormation

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
