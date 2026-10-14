import Solcore.SourceSemantics.SourceInferenceSelectedInferenceSupport

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
namespace InferenceSupport
open Detail

theorem addRequirements_resolve (state : State) (predicates : List ProgramPredicate) (type : Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type = state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [State.addRequirementsWithIds]
      rw [induction]
      rfl

private abbrev finishOperator (context : Frontend.SourceInference.Context) (dispatch : OperatorDispatch)
    (operand builtin builtinResult resultType : Ty)
    (parameterTypes : List Ty) (hasOpenLiteralOperand : Bool)
    (state : State) : Except Error OperatorInferenceResult :=
  if operand = builtin then
    pure {
      type := builtinResult
      requirements := []
      state
    }
  else
    match dispatch with
    | .function name =>
        if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := resultType
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
        match ← operatorTrait? context traitName with
        | some trait =>
            let predicates ← operatorTraitPredicates context trait methodName
              operand parameterTypes [resultType]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure {
              type := resultType
              requirements
              state
            }
        | none =>
            if isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                  builtin operand ||
                isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                  builtin operand then
              pure {
                type := resultType
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {dispatch : OperatorDispatch}
    {operand builtin builtinResult resultType : Ty}
    {parameterTypes : List Ty} {hasOpenLiteralOperand : Bool}
    {state : State} {result : OperatorInferenceResult}
    (builtinSupported : Resolved cutoff roots state builtinResult)
    (resultSupported : Resolved cutoff roots state resultType)
    (success : finishOperator context dispatch operand builtin builtinResult
      resultType parameterTypes hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  unfold finishOperator at success
  by_cases builtinMatch : operand = builtin
  · simp only [builtinMatch, if_true] at success
    injection success with resultEq
    subst result
    exact ⟨.refl _ _ _, builtinSupported⟩
  · simp only [builtinMatch, if_false] at success
    cases dispatch with
    | function name =>
        cases deferredResult :
            (isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
                builtin operand ||
              isStagedIntegerOperatorTarget state hasOpenLiteralOperand
                builtin operand) with
        | false =>
          simp [deferredResult] at success
        | true =>
          simp only [deferredResult, if_true] at success
          injection success with resultEq
          subst result
          exact ⟨.refl _ _ _, resultSupported⟩
    | traitMethod traitName methodName =>
        cases traitResult : operatorTrait? context traitName with
        | error error =>
            simp [traitResult, bind, Except.bind] at success
        | ok traitOption =>
            cases traitOption with
            | none =>
                simp only [traitResult, bind, Except.bind] at success
                cases deferredResult :
                    (isDeferredBuiltinOperatorTarget state
                        hasOpenLiteralOperand builtin operand ||
                      isStagedIntegerOperatorTarget state
                        hasOpenLiteralOperand builtin operand) with
                | false =>
                  simp [deferredResult] at success
                | true =>
                  simp only [deferredResult, if_true] at success
                  injection success with resultEq
                  subst result
                  exact ⟨.refl _ _ _, resultSupported⟩
            | some trait =>
                simp only [traitResult, bind, Except.bind] at success
                cases predicatesResult : operatorTraitPredicates context trait
                    methodName operand parameterTypes [resultType] with
                | error error =>
                    simp [predicatesResult] at success
                | ok predicates =>
                    simp only [predicatesResult] at success
                    change Except.ok {
                      type := resultType
                      requirements :=
                        (state.addRequirementsWithIds predicates).1
                      state := (state.addRequirementsWithIds predicates).2
                    } = Except.ok result at success
                    injection success with resultEq
                    subst result
                    have transport : Transport cutoff roots state
                        (state.addRequirementsWithIds predicates).2 :=
                      .of_resolve_eq (addRequirements_resolve state predicates)
                    exact ⟨transport, transport resultType resultSupported⟩

private def unaryBuiltin : Syntax.UnaryOp → Ty
  | .logicalNot => .bool
  | .bitNot => .word

private abbrev finishUnaryOperator (context : Frontend.SourceInference.Context)
    (operator : Syntax.UnaryOp) (operandType : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve operandType
  let builtin := unaryBuiltin operator
  finishOperator context (unaryOperatorDispatch operator) operand builtin
    builtin (if operator == Syntax.UnaryOp.logicalNot then .bool else operand)
    [operand] hasOpenLiteralOperand state

private abbrev finishBinaryOperator (context : Frontend.SourceInference.Context)
    (operator : Syntax.BinaryOp) (left : Ty)
    (hasOpenLiteralOperand : Bool) (state : State) :
    Except Error OperatorInferenceResult :=
  let operand := state.resolve left
  let builtin := binaryBuiltinType operator
  finishOperator context (binaryOperatorDispatch operator) operand builtin
    (if binaryResultIsBool operator then .bool else builtin)
    (if binaryResultIsBool operator then .bool else operand)
    [operand, operand] hasOpenLiteralOperand state

private theorem finishUnaryOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.UnaryOp}
    {operandType : Ty} {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state operandType)
    (success : finishUnaryOperator context operator operandType
      hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  have builtin : Resolved cutoff roots state
      (unaryBuiltin operator) := by
    exact resolved_closed _ _ _ (by cases operator <;> rfl)
  have output : Resolved cutoff roots state
      (if operator == Syntax.UnaryOp.logicalNot then .bool else state.resolve operandType) := by
    split
    · exact resolved_closed _ _ _ rfl
    · exact resolved_normalized ready supported
  exact finishOperator_supported builtin output success

private theorem finishBinaryOperator_supported
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.BinaryOp}
    {left : Ty} {hasOpenLiteralOperand : Bool} {state : State}
    {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (supported : Resolved cutoff roots state left)
    (success : finishBinaryOperator context operator left
      hasOpenLiteralOperand state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  have builtin : Resolved cutoff roots state
      (if binaryResultIsBool operator then .bool else binaryBuiltinType operator) := by
    split
    · exact resolved_closed _ _ _ rfl
    · cases operator <;> exact resolved_closed _ _ _ rfl
  have output : Resolved cutoff roots state
      (if binaryResultIsBool operator then .bool else state.resolve left) := by
    split
    · exact resolved_closed _ _ _ rfl
    · exact resolved_normalized ready supported
  exact finishOperator_supported (context := context) builtin output
    (by simpa only [finishBinaryOperator] using success)

theorem inferUnaryOperator
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandBelow : operandType.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (operandSupported : Resolved cutoff roots state operandType)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (success : Detail.inferUnaryOperator context operator operandType expected
      integerLiterals state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at success
  cases expected with
  | none =>
      simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at success
      have tailSuccess : finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result := by
        change finishUnaryOperator context operator operandType
          hasOpenLiteralOperand state = .ok result at success
        exact success
      exact finishUnaryOperator_supported ready operandSupported
        tailSuccess
  | some expectedType =>
      have expectedTypeBelow := expectedBelow expectedType (by simp)
      cases skipResult :
          (operator == Syntax.UnaryOp.logicalNot ||
            (state.resolve operandType).freeVariables.isEmpty ||
              !hasOpenLiteralOperand) with
      | true =>
          simp only [hasOpenLiteralOperand, skipResult, if_true, bind,
            Except.bind, pure, Pure.pure, Except.pure] at success
          have tailSuccess : finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result := by
            change finishUnaryOperator context operator operandType
              hasOpenLiteralOperand state = .ok result at success
            exact success
          exact finishUnaryOperator_supported ready operandSupported
            tailSuccess
      | false =>
          simp only [hasOpenLiteralOperand, skipResult, Bool.false_eq_true,
            if_false] at success
          cases unifyResult : Detail.unify state (state.resolve operandType)
              expectedType with
          | error error =>
              simp [unifyResult, bind, Except.bind] at success
          | ok fittedState =>
              simp only [unifyResult, bind, Except.bind] at success
              have resolvedOperandBelow :
                  (state.resolve operandType).VariablesBelow
                    state.inference.next :=
                ready.solved.variablesBelow_apply operandBelow
              have transport := unify ready resolvedOperandBelow expectedTypeBelow
                (resolved_normalized ready operandSupported)
                (expectedSupported expectedType (by simp)) unifyResult
              have fittedReady := unify_preserves_inferenceReady ready
                resolvedOperandBelow expectedTypeBelow unifyResult
              have tailSuccess : finishUnaryOperator context operator
                  operandType hasOpenLiteralOperand fittedState = .ok result := by
                change finishUnaryOperator context operator operandType
                  hasOpenLiteralOperand fittedState = .ok result at success
                exact success
              have tailProperties :=
                finishUnaryOperator_supported fittedReady
                  (transport operandType operandSupported) tailSuccess
              exact ⟨transport.trans tailProperties.1, tailProperties.2⟩

theorem inferBinaryOperator
    {cutoff : Nat} {roots : List Ty} {context : Frontend.SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (expectedBelow : ∀ expectedType ∈ expected,
      expectedType.VariablesBelow state.inference.next)
    (leftSupported : Resolved cutoff roots state left)
    (rightSupported : Resolved cutoff roots state right)
    (expectedSupported : ∀ type ∈ expected, Resolved cutoff roots state type)
    (success : Detail.inferBinaryOperator context operator left right expected
      integerLiterals state = .ok result) :
    Transport cutoff roots state result.state ∧
      Resolved cutoff roots result.state result.type := by
  let hasOpenLiteralOperand :=
    isOpenIntegerLiteralTarget state integerLiterals left ||
      isOpenIntegerLiteralTarget state integerLiterals right
  unfold Detail.inferBinaryOperator at success
  cases unifyResult : Detail.unify state left right with
  | error error =>
      simp [unifyResult, bind, Except.bind] at success
  | ok unifiedState =>
      simp only [unifyResult, bind, Except.bind] at success
      have unifyProgress := unify_inferenceProgress ready.solved leftBelow
        rightBelow unifyResult
      have transport := unify ready leftBelow rightBelow leftSupported rightSupported unifyResult
      have unifiedReady := unify_preserves_inferenceReady ready leftBelow
        rightBelow unifyResult
      have leftAtUnified :
          left.VariablesBelow unifiedState.inference.next :=
        leftBelow.weaken unifyProgress.next_le
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          have tailSuccess : finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result := by
            change finishBinaryOperator context operator left
              hasOpenLiteralOperand unifiedState = .ok result at success
            exact success
          have tailProperties := finishBinaryOperator_supported
            unifiedReady (transport left leftSupported) tailSuccess
          exact ⟨transport.trans tailProperties.1,
            tailProperties.2⟩
      | some expectedType =>
          have expectedTypeBelow : expectedType.VariablesBelow
              unifiedState.inference.next :=
            (expectedBelow expectedType (by simp)).weaken
              unifyProgress.next_le
          cases skipResult :
              (binaryResultIsBool operator ||
                (unifiedState.resolve left).freeVariables.isEmpty ||
                  !hasOpenLiteralOperand) with
          | true =>
              simp only [hasOpenLiteralOperand, skipResult, if_true,
                pure, Pure.pure, Except.pure] at success
              have tailSuccess : finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result := by
                change finishBinaryOperator context operator left
                  hasOpenLiteralOperand unifiedState = .ok result at success
                exact success
              have tailProperties := finishBinaryOperator_supported
                unifiedReady (transport left leftSupported) tailSuccess
              exact ⟨transport.trans tailProperties.1,
                tailProperties.2⟩
          | false =>
              simp only [hasOpenLiteralOperand, skipResult,
                Bool.false_eq_true, if_false] at success
              have resolvedLeftBelow :
                  (unifiedState.resolve left).VariablesBelow
                    unifiedState.inference.next :=
                unifiedReady.solved.variablesBelow_apply leftAtUnified
              cases fittedResult : Detail.unify unifiedState
                  (unifiedState.resolve left) expectedType with
              | error error =>
                  simp [fittedResult] at success
              | ok fittedState =>
                  simp only [fittedResult] at success
                  have secondTransport := unify unifiedReady resolvedLeftBelow expectedTypeBelow
                    (resolved_normalized unifiedReady (transport left leftSupported))
                    (transport expectedType (expectedSupported expectedType (by simp))) fittedResult
                  have fittedReady := unify_preserves_inferenceReady
                    unifiedReady resolvedLeftBelow expectedTypeBelow fittedResult
                  have tailSuccess : finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result := by
                    change finishBinaryOperator context operator left
                      hasOpenLiteralOperand fittedState = .ok result at success
                    exact success
                  have tailProperties :=
                    finishBinaryOperator_supported fittedReady
                      (secondTransport left (transport left leftSupported)) tailSuccess
                  exact ⟨transport.trans (secondTransport.trans tailProperties.1),
                    tailProperties.2⟩

end InferenceSupport
end Solcore.SourceSemantics.SourceInferenceSoundness
