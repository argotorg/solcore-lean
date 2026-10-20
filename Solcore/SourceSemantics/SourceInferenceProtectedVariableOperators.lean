import Solcore.SourceSemantics.SourceInferenceProtectedVariableArguments

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

private abbrev finishOperator (context : SourceInference.Context) (dispatch : Detail.OperatorDispatch)
    (operand builtin builtinResult resultType : Ty) (parameterTypes : List Ty)
    (hasOpenLiteralOperand : Bool) (state : State) : Except Error Detail.OperatorInferenceResult :=
  if operand = builtin then
    pure {type := builtinResult, requirements := [], state}
  else
    match dispatch with
    | .function name =>
      if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
          Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
        pure {type := resultType, requirements := [], state}
      else throw (.unknownVariable name)
    | .traitMethod traitName methodName => do
      match ← Detail.operatorTrait? context traitName with
      | some trait =>
        let predicates ← Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType]
        let (requirements,state) := state.addRequirementsWithIds predicates
        pure {type := resultType, requirements, state}
      | none =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand builtin operand then
          pure {type := resultType, requirements := [], state}
        else throw (.operatorNotSupported traitName operand)

private abbrev finishUnary (context : SourceInference.Context) (operator : Syntax.UnaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := match operator with | .logicalNot => Ty.bool | .bitNot => Ty.word
  finishOperator context (Detail.unaryOperatorDispatch operator) operand builtin builtin
    (if operator == Syntax.UnaryOp.logicalNot then .bool else operand) [operand] hasOpenLiteralOperand state

private abbrev finishBinary (context : SourceInference.Context) (operator : Syntax.BinaryOp)
    (operandType : Ty) (hasOpenLiteralOperand : Bool) (state : State) :=
  let operand := state.resolve operandType
  let builtin := Detail.binaryBuiltinType operator
  finishOperator context (Detail.binaryOperatorDispatch operator) operand builtin
    (if Detail.binaryResultIsBool operator then .bool else builtin)
    (if Detail.binaryResultIsBool operator then .bool else operand)
    [operand,operand] hasOpenLiteralOperand state

private theorem finishOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {dispatch : Detail.OperatorDispatch}
    {operand builtin builtinResult resultType : Ty} {parameterTypes : List Ty}
    {hasOpenLiteralOperand : Bool} {state : State} {result : Detail.OperatorInferenceResult}
    (fixed : FixesProtected protectedVars state)
    (accepted : finishOperator context dispatch operand builtin builtinResult resultType
      parameterTypes hasOpenLiteralOperand state = .ok result) :
    FixesProtected protectedVars result.state := by
  unfold finishOperator at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact fixed
  · cases dispatch with
    | function name =>
      simp only at accepted
      split at accepted
      · cases Except.ok.inj accepted
        exact fixed
      · cases accepted
    | traitMethod traitName methodName =>
      cases traitResult : Detail.operatorTrait? context traitName with
      | error error => simp [traitResult, bind, Except.bind] at accepted
      | ok option =>
        cases option with
        | none =>
          simp only [traitResult, bind, Except.bind] at accepted
          split at accepted
          · cases Except.ok.inj accepted
            exact fixed
          · cases accepted
        | some trait =>
          simp only [traitResult, bind, Except.bind] at accepted
          cases predicatesResult : Detail.operatorTraitPredicates context trait methodName operand parameterTypes [resultType] with
          | error error => simp [predicatesResult] at accepted
          | ok predicates =>
            simp only [predicatesResult, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
            cases accepted
            exact fixed.of_substitution_eq (congrArg InferState.substitution (requirementBatch_inference _ _))

theorem inferUnaryOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.UnaryOp} {operandType : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (operandSafe : Safe protectedVars state operandType)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferUnaryOperator context operator operandType expected integerLiterals state = .ok result) :
    FixesProtected protectedVars result.state := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals operandType
  unfold Detail.inferUnaryOperator at accepted
  cases expected with
  | none =>
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    exact finishOperator_fixes_protected fixed (show finishUnary context operator operandType openLiteral state = .ok result from accepted)
  | some expectedType =>
    have expectedSafe := expectedSafe expectedType (by simp)
    cases skip : (operator == Syntax.UnaryOp.logicalNot ||
        (state.resolve operandType).freeVariables.isEmpty || !openLiteral) with
    | true =>
      simp only [openLiteral, skip, if_true, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      exact finishOperator_fixes_protected fixed (show finishUnary context operator operandType openLiteral state = .ok result from accepted)
    | false =>
      simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
      cases unified : Detail.unify state (state.resolve operandType) expectedType with
      | error error => simp [unified, bind, Except.bind] at accepted
      | ok fitted =>
        simp only [unified, bind, Except.bind] at accepted
        have fittedFixed := unify_fixes_protected fixed (safe_resolved ready operandSafe) expectedSafe unified
        exact finishOperator_fixes_protected fittedFixed (show finishUnary context operator operandType openLiteral fitted = .ok result from accepted)

theorem inferBinaryOperator_fixes_protected {protectedVars : List TypeVarId}
    {context : SourceInference.Context} {operator : Syntax.BinaryOp} {left right : Ty}
    {expected : Option Ty} {integerLiterals : List IntegerLiteralOrigin}
    {state : State} {result : Detail.OperatorInferenceResult}
    (ready : state.InferenceReady)
    (leftBelow : left.VariablesBelow state.inference.next)
    (rightBelow : right.VariablesBelow state.inference.next)
    (leftSafe : Safe protectedVars state left) (rightSafe : Safe protectedVars state right)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.inferBinaryOperator context operator left right expected integerLiterals state = .ok result) :
    FixesProtected protectedVars result.state := by
  let openLiteral := Detail.isOpenIntegerLiteralTarget state integerLiterals left ||
    Detail.isOpenIntegerLiteralTarget state integerLiterals right
  unfold Detail.inferBinaryOperator at accepted
  cases unified : Detail.unify state left right with
  | error error => simp [unified, bind, Except.bind] at accepted
  | ok unifiedState =>
    simp only [unified, bind, Except.bind] at accepted
    have unifiedReady := Detail.unify_preserves_inferenceReady ready leftBelow rightBelow unified
    have unifiedPrivacy := ProtectedVariables.unify leftSafe rightSafe unified
    have operandSafe := unifiedPrivacy _ leftSafe
    have unifiedFixed := unify_fixes_protected fixed leftSafe rightSafe unified
    cases expected with
    | none =>
      simp only [pure, Pure.pure, Except.pure] at accepted
      exact finishOperator_fixes_protected unifiedFixed (show finishBinary context operator left openLiteral unifiedState = .ok result from accepted)
    | some expectedType =>
      have expectedSafe := unifiedPrivacy _ (expectedSafe expectedType (by simp))
      cases skip : (Detail.binaryResultIsBool operator ||
          (unifiedState.resolve left).freeVariables.isEmpty || !openLiteral) with
      | true =>
        simp only [openLiteral, skip, if_true, pure, Pure.pure, Except.pure] at accepted
        exact finishOperator_fixes_protected unifiedFixed (show finishBinary context operator left openLiteral unifiedState = .ok result from accepted)
      | false =>
        simp only [openLiteral, skip, Bool.false_eq_true, if_false] at accepted
        cases fitted : Detail.unify unifiedState (unifiedState.resolve left) expectedType with
        | error error => simp [fitted] at accepted
        | ok fittedState =>
          simp only [fitted] at accepted
          have fittedFixed := unify_fixes_protected unifiedFixed (safe_resolved unifiedReady operandSafe) expectedSafe fitted
          exact finishOperator_fixes_protected fittedFixed (show finishBinary context operator left openLiteral fittedState = .ok result from accepted)

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
