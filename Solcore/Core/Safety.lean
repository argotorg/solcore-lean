import Solcore.Core.Correspondence

set_option autoImplicit false

namespace Solcore.Core

mutual

  inductive ValueHasType : Value → Ty → Prop where
    | unit : ValueHasType .unit .unit
    | bool {value : Bool} : ValueHasType (.bool value) .bool
    | word {value : Word} : ValueHasType (.word value) .word
    | pair
        {left right : Value} {leftType rightType : Ty} :
        ValueHasType left leftType →
        ValueHasType right rightType →
        ValueHasType (.pair left right) (.product leftType rightType)
    | inLeft
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload leftType →
        ValueHasType (.inLeft rightType payload) (.sum leftType rightType)
    | inRight
        {payload : Value} {leftType rightType : Ty} :
        ValueHasType payload rightType →
        ValueHasType (.inRight leftType payload) (.sum leftType rightType)
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} {context : Context} :
        EnvironmentHasTypes environment context →
        HasType (parameterType :: context) body resultType →
        ValueHasType
          (.closure parameterType resultType body environment)
          (.function parameterType resultType)

  inductive EnvironmentHasTypes : Environment → Context → Prop where
    | nil : EnvironmentHasTypes [] []
    | cons
        {value : Value} {type : Ty}
        {environment : Environment} {context : Context} :
        ValueHasType value type →
        EnvironmentHasTypes environment context →
        EnvironmentHasTypes (value :: environment) (type :: context)

end

theorem EnvironmentHasTypes.lookup
    {environment : Environment} {context : Context}
    (hasTypes : EnvironmentHasTypes environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value, environment[index]? = some value ∧ ValueHasType value type := by
  induction hasTypes using EnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ => True) generalizing index with
  | unit | bool | word | pair | inLeft | inRight | closure => exact True.intro
  | nil =>
      simp at typeLookup
  | cons valueTyping tailTyping _ tailIH =>
      cases index with
      | zero =>
          simp at typeLookup
          cases typeLookup
          exact ⟨_, rfl, valueTyping⟩
      | succ index =>
          simp at typeLookup
          obtain ⟨value, valueLookup, valueTyping⟩ := tailIH typeLookup
          exact ⟨value, by simpa using valueLookup, valueTyping⟩

theorem ValueHasType.bool_shape
    {value : Value}
    (typing : ValueHasType value .bool) :
    ∃ decision, value = .bool decision := by
  cases typing with
  | bool => exact ⟨_, rfl⟩

theorem ValueHasType.type_eq
    {value : Value} {type : Ty}
    (typing : ValueHasType value type) :
    value.type = type := by
  induction typing using ValueHasType.rec
      (motive_2 := fun _ _ _ => True) with
  | unit | bool | word | closure => rfl
  | pair leftTyping rightTyping leftIH rightIH =>
      simp [Value.type, leftIH, rightIH]
  | inLeft payloadTyping payloadIH =>
      simp [Value.type, payloadIH]
  | inRight payloadTyping payloadIH =>
      simp [Value.type, payloadIH]
  | nil | cons => exact True.intro

theorem unary_apply_result_has_type
    {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    ValueHasType result op.resultType := by
  cases op <;> cases operand <;>
    simp [UnaryOp.apply] at applied <;>
    cases applied <;> constructor

theorem binary_apply_result_has_type
    {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    ValueHasType result op.resultType := by
  cases op <;> cases left <;> cases right <;>
    simp [BinaryOp.apply] at applied <;>
    cases applied <;> constructor

theorem evaluation_preserves_type
    {environment : Environment} {context : Context}
    {expr : Expr} {value : Value} {type : Ty}
    (evaluation : Evaluates environment expr value)
    (typing : HasType context expr type)
    (environmentTyping : EnvironmentHasTypes environment context) :
    ValueHasType value type := by
  induction evaluation generalizing context type with
  | unit =>
      cases typing
      exact .unit
  | bool =>
      cases typing
      exact .bool
  | word =>
      cases typing
      exact .word
  | pair leftEvaluation rightEvaluation leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          exact .pair
            (leftIH leftTyping environmentTyping)
            (rightIH rightTyping environmentTyping)
  | first operandEvaluation operandIH =>
      cases typing with
      | first operandTyping =>
          have operandValueTyping :=
            operandIH operandTyping environmentTyping
          cases operandValueTyping with
          | pair leftTyping rightTyping => exact leftTyping
  | second operandEvaluation operandIH =>
      cases typing with
      | second operandTyping =>
          have operandValueTyping :=
            operandIH operandTyping environmentTyping
          cases operandValueTyping with
          | pair leftTyping rightTyping => exact rightTyping
  | inLeft payloadEvaluation payloadIH =>
      cases typing with
      | inLeft payloadTyping =>
          exact .inLeft (payloadIH payloadTyping environmentTyping)
  | inRight payloadEvaluation payloadIH =>
      cases typing with
      | inRight payloadTyping =>
          exact .inRight (payloadIH payloadTyping environmentTyping)
  | caseLeft scrutineeEvaluation branchEvaluation scrutineeIH branchIH =>
      cases typing with
      | caseE scrutineeTyping leftTyping rightTyping =>
          have scrutineeValueTyping :=
            scrutineeIH scrutineeTyping environmentTyping
          cases scrutineeValueTyping with
          | inLeft payloadTyping =>
              exact branchIH
                leftTyping
                (.cons payloadTyping environmentTyping)
  | caseRight scrutineeEvaluation branchEvaluation scrutineeIH branchIH =>
      cases typing with
      | caseE scrutineeTyping leftTyping rightTyping =>
          have scrutineeValueTyping :=
            scrutineeIH scrutineeTyping environmentTyping
          cases scrutineeValueTyping with
          | inRight payloadTyping =>
              exact branchIH
                rightTyping
                (.cons payloadTyping environmentTyping)
  | lambda =>
      cases typing with
      | lambda bodyTyping => exact .closure environmentTyping bodyTyping
  | apply functionEvaluation argumentEvaluation bodyEvaluation
      functionIH argumentIH bodyIH =>
      cases typing with
      | apply functionTyping argumentTyping =>
          have functionValueTyping :=
            functionIH functionTyping environmentTyping
          cases functionValueTyping with
          | closure capturedEnvironmentTyping bodyTyping =>
              have argumentValueTyping :=
                argumentIH argumentTyping environmentTyping
              exact bodyIH
                bodyTyping
                (.cons argumentValueTyping capturedEnvironmentTyping)
  | var valueLookup =>
      cases typing with
      | var typeLookup =>
          obtain ⟨found, foundLookup, foundTyping⟩ :=
            environmentTyping.lookup typeLookup
          rw [valueLookup] at foundLookup
          cases foundLookup
          exact foundTyping
  | unary operandEvaluation applied operandIH =>
      cases typing with
      | unary operandTyping =>
          exact unary_apply_result_has_type applied
  | binary leftEvaluation rightEvaluation applied leftIH rightIH =>
      cases typing with
      | binary leftTyping rightTyping =>
          exact binary_apply_result_has_type applied
  | letE boundEvaluation bodyEvaluation boundIH bodyIH =>
      cases typing with
      | letE boundTyping bodyTyping =>
          have boundValueTyping :=
            boundIH boundTyping environmentTyping
          exact bodyIH bodyTyping (.cons boundValueTyping environmentTyping)
  | ifTrue conditionEvaluation branchEvaluation conditionIH branchIH =>
      cases typing with
      | ifE conditionTyping thenTyping elseTyping =>
          exact branchIH thenTyping environmentTyping
  | ifFalse conditionEvaluation branchEvaluation conditionIH branchIH =>
      cases typing with
      | ifE conditionTyping thenTyping elseTyping =>
          exact branchIH elseTyping environmentTyping

def ReducibleValue : (type : Ty) → Value → Prop
  | .unit, value => value = .unit
  | .bool, value => ∃ decision, value = .bool decision
  | .word, value => ∃ word, value = .word word
  | .product leftType rightType, value =>
      ∃ left right,
        value = .pair left right ∧
        ReducibleValue leftType left ∧
        ReducibleValue rightType right
  | .sum leftType rightType, value =>
      (∃ payload,
        value = .inLeft rightType payload ∧
        ReducibleValue leftType payload) ∨
      (∃ payload,
        value = .inRight leftType payload ∧
        ReducibleValue rightType payload)
  | .function parameterType resultType, value =>
      ∃ body environment context,
        value = .closure parameterType resultType body environment ∧
        EnvironmentHasTypes environment context ∧
        HasType (parameterType :: context) body resultType ∧
        ∀ argument,
          ReducibleValue parameterType argument →
          ∃ result,
            Evaluates (argument :: environment) body result ∧
            ReducibleValue resultType result
termination_by type _ => type

inductive ReducibleEnvironment : Environment → Context → Prop where
  | nil : ReducibleEnvironment [] []
  | cons
      {value : Value} {type : Ty}
      {environment : Environment} {context : Context} :
      ReducibleValue type value →
      ReducibleEnvironment environment context →
      ReducibleEnvironment (value :: environment) (type :: context)

theorem ReducibleEnvironment.lookup
    {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value,
      environment[index]? = some value ∧ ReducibleValue type value := by
  induction reducible generalizing index with
  | nil => simp at typeLookup
  | cons headReducible tailReducible tailIH =>
      cases index with
      | zero =>
          simp at typeLookup
          cases typeLookup
          exact ⟨_, rfl, headReducible⟩
      | succ index =>
          simp at typeLookup
          obtain ⟨value, valueLookup, valueReducible⟩ := tailIH typeLookup
          exact ⟨value, by simpa using valueLookup, valueReducible⟩

theorem ReducibleValue.hasType
    {type : Ty} {value : Value}
    (reducible : ReducibleValue type value) :
    ValueHasType value type := by
  induction type generalizing value with
  | unit =>
      simp only [ReducibleValue] at reducible
      subst value
      exact .unit
  | bool =>
      simp only [ReducibleValue] at reducible
      obtain ⟨decision, rfl⟩ := reducible
      exact .bool
  | word =>
      simp only [ReducibleValue] at reducible
      obtain ⟨word, rfl⟩ := reducible
      exact .word
  | product leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible
      obtain ⟨left, right, rfl, leftReducible, rightReducible⟩ := reducible
      exact .pair (leftIH leftReducible) (rightIH rightReducible)
  | function parameterType resultType parameterIH resultIH =>
      simp only [ReducibleValue] at reducible
      obtain ⟨body, environment, context, rfl,
        environmentTyping, bodyTyping, _⟩ := reducible
      exact .closure environmentTyping bodyTyping
  | sum leftType rightType leftIH rightIH =>
      simp only [ReducibleValue] at reducible
      cases reducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          exact .inLeft (leftIH payloadReducible)
      | inr rightReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := rightReducible
          exact .inRight (rightIH payloadReducible)

theorem ReducibleEnvironment.hasTypes
    {environment : Environment} {context : Context}
    (reducible : ReducibleEnvironment environment context) :
    EnvironmentHasTypes environment context := by
  induction reducible with
  | nil => exact .nil
  | cons headReducible tailReducible tailIH =>
      exact .cons headReducible.hasType tailIH

theorem ValueHasType.bool_reducible
    {value : Value}
    (typing : ValueHasType value .bool) :
    ReducibleValue .bool value := by
  cases typing with
  | bool =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩

theorem ValueHasType.word_reducible
    {value : Value}
    (typing : ValueHasType value .word) :
    ReducibleValue .word value := by
  cases typing with
  | word =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩

theorem unary_apply_result_reducible
    {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    ReducibleValue op.resultType result := by
  cases op with
  | boolNot =>
      change ReducibleValue .bool result
      exact (unary_apply_result_has_type applied).bool_reducible
  | wordNot =>
      change ReducibleValue .word result
      exact (unary_apply_result_has_type applied).word_reducible

theorem binary_apply_result_reducible
    {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    ReducibleValue op.resultType result := by
  cases op <;>
    first
    | exact (binary_apply_result_has_type applied).bool_reducible
    | exact (binary_apply_result_has_type applied).word_reducible

theorem reducibility_fundamental
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {environment : Environment}
    (environmentReducible : ReducibleEnvironment environment context) :
    ∃ value,
      Evaluates environment expr value ∧ ReducibleValue type value := by
  induction typing generalizing environment with
  | unit =>
      refine ⟨.unit, .unit, ?_⟩
      simp only [ReducibleValue]
  | bool =>
      refine ⟨.bool _, .bool, ?_⟩
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | word =>
      refine ⟨.word _, .word, ?_⟩
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | var typeLookup =>
      obtain ⟨value, valueLookup, valueReducible⟩ :=
        environmentReducible.lookup typeLookup
      exact ⟨value, .var valueLookup, valueReducible⟩
  | pair leftTyping rightTyping leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftReducible⟩ :=
        leftIH environmentReducible
      obtain ⟨rightValue, rightEvaluation, rightReducible⟩ :=
        rightIH environmentReducible
      refine ⟨.pair leftValue rightValue,
        .pair leftEvaluation rightEvaluation, ?_⟩
      simp only [ReducibleValue]
      exact ⟨leftValue, rightValue, rfl, leftReducible, rightReducible⟩
  | first operandTyping operandIH =>
      obtain ⟨operandValue, operandEvaluation, operandReducible⟩ :=
        operandIH environmentReducible
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl,
        leftReducible, rightReducible⟩ := operandReducible
      exact ⟨leftValue, .first operandEvaluation, leftReducible⟩
  | second operandTyping operandIH =>
      obtain ⟨operandValue, operandEvaluation, operandReducible⟩ :=
        operandIH environmentReducible
      simp only [ReducibleValue] at operandReducible
      obtain ⟨leftValue, rightValue, rfl,
        leftReducible, rightReducible⟩ := operandReducible
      exact ⟨rightValue, .second operandEvaluation, rightReducible⟩
  | @lambda context parameterType resultType body bodyTyping bodyIH =>
      refine ⟨.closure parameterType resultType body environment, .lambda, ?_⟩
      simp only [ReducibleValue]
      exact ⟨body, environment, context, rfl,
        environmentReducible.hasTypes, bodyTyping,
        fun argument argumentReducible =>
          bodyIH (.cons argumentReducible environmentReducible)⟩
  | @apply context function argument parameterType resultType
      functionTyping argumentTyping functionIH argumentIH =>
      obtain ⟨functionValue, functionEvaluation, functionReducible⟩ :=
        functionIH environmentReducible
      simp only [ReducibleValue] at functionReducible
      obtain ⟨body, capturedEnvironment, capturedContext,
        functionShape, capturedTyping, bodyTyping, callable⟩ := functionReducible
      subst functionValue
      obtain ⟨argumentValue, argumentEvaluation, argumentReducible⟩ :=
        argumentIH environmentReducible
      obtain ⟨result, bodyEvaluation, resultReducible⟩ :=
        callable argumentValue argumentReducible
      exact ⟨result,
        .apply functionEvaluation argumentEvaluation bodyEvaluation,
        resultReducible⟩
  | @inLeft context rightType leftType payload payloadTyping payloadIH =>
      obtain ⟨payloadValue, payloadEvaluation, payloadReducible⟩ :=
        payloadIH environmentReducible
      refine ⟨.inLeft rightType payloadValue,
        .inLeft payloadEvaluation, ?_⟩
      simp only [ReducibleValue]
      exact .inl ⟨payloadValue, rfl, payloadReducible⟩
  | @inRight context leftType rightType payload payloadTyping payloadIH =>
      obtain ⟨payloadValue, payloadEvaluation, payloadReducible⟩ :=
        payloadIH environmentReducible
      refine ⟨.inRight leftType payloadValue,
        .inRight payloadEvaluation, ?_⟩
      simp only [ReducibleValue]
      exact .inr ⟨payloadValue, rfl, payloadReducible⟩
  | @caseE context scrutinee leftBranch rightBranch
      leftType rightType resultType
      scrutineeTyping leftTyping rightTyping
      scrutineeIH leftIH rightIH =>
      obtain ⟨scrutineeValue, scrutineeEvaluation, scrutineeReducible⟩ :=
        scrutineeIH environmentReducible
      simp only [ReducibleValue] at scrutineeReducible
      cases scrutineeReducible with
      | inl leftReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := leftReducible
          obtain ⟨result, branchEvaluation, resultReducible⟩ :=
            leftIH (.cons payloadReducible environmentReducible)
          exact ⟨result,
            .caseLeft scrutineeEvaluation branchEvaluation,
            resultReducible⟩
      | inr rightReducible =>
          obtain ⟨payload, rfl, payloadReducible⟩ := rightReducible
          obtain ⟨result, branchEvaluation, resultReducible⟩ :=
            rightIH (.cons payloadReducible environmentReducible)
          exact ⟨result,
            .caseRight scrutineeEvaluation branchEvaluation,
            resultReducible⟩
  | unary operandTyping operandIH =>
      obtain ⟨operandValue, operandEvaluation, operandReducible⟩ :=
        operandIH environmentReducible
      obtain ⟨result, applied, _⟩ :=
        UnaryOp.apply_total_of_type
          _ operandValue operandReducible.hasType.type_eq
      exact ⟨result, .unary operandEvaluation applied,
        unary_apply_result_reducible applied⟩
  | binary leftTyping rightTyping leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation, leftReducible⟩ :=
        leftIH environmentReducible
      obtain ⟨rightValue, rightEvaluation, rightReducible⟩ :=
        rightIH environmentReducible
      obtain ⟨result, applied, _⟩ :=
        BinaryOp.apply_total_of_types
          _ leftValue rightValue
          leftReducible.hasType.type_eq rightReducible.hasType.type_eq
      exact ⟨result, .binary leftEvaluation rightEvaluation applied,
        binary_apply_result_reducible applied⟩
  | letE boundTyping bodyTyping boundIH bodyIH =>
      obtain ⟨boundValue, boundEvaluation, boundReducible⟩ :=
        boundIH environmentReducible
      obtain ⟨result, bodyEvaluation, resultReducible⟩ :=
        bodyIH (.cons boundReducible environmentReducible)
      exact ⟨result, .letE boundEvaluation bodyEvaluation, resultReducible⟩
  | ifE conditionTyping thenTyping elseTyping conditionIH thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionReducible⟩ :=
        conditionIH environmentReducible
      simp only [ReducibleValue] at conditionReducible
      obtain ⟨decision, rfl⟩ := conditionReducible
      cases decision with
      | false =>
          obtain ⟨result, branchEvaluation, resultReducible⟩ :=
            elseIH environmentReducible
          exact ⟨result, .ifFalse conditionEvaluation branchEvaluation,
            resultReducible⟩
      | true =>
          obtain ⟨result, branchEvaluation, resultReducible⟩ :=
            thenIH environmentReducible
          exact ⟨result, .ifTrue conditionEvaluation branchEvaluation,
            resultReducible⟩

theorem ValueHasType.reducible
    {value : Value} {type : Ty}
    (typing : ValueHasType value type) :
    ReducibleValue type value := by
  induction typing using ValueHasType.rec
      (motive_2 := fun environment context _ =>
        ReducibleEnvironment environment context) with
  | unit => simp only [ReducibleValue]
  | bool =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | word =>
      simp only [ReducibleValue]
      exact ⟨_, rfl⟩
  | pair leftTyping rightTyping leftIH rightIH =>
      simp only [ReducibleValue]
      exact ⟨_, _, rfl, leftIH, rightIH⟩
  | inLeft payloadTyping payloadIH =>
      simp only [ReducibleValue]
      exact .inl ⟨_, rfl, payloadIH⟩
  | inRight payloadTyping payloadIH =>
      simp only [ReducibleValue]
      exact .inr ⟨_, rfl, payloadIH⟩
  | @closure parameterType resultType body environment context
      environmentTyping bodyTyping environmentIH =>
      simp only [ReducibleValue]
      exact ⟨body, environment, context, rfl,
        environmentTyping, bodyTyping,
        fun argument argumentReducible =>
          reducibility_fundamental
            bodyTyping
            (.cons argumentReducible environmentIH)⟩
  | nil => exact .nil
  | cons valueTyping environmentTyping valueIH environmentIH =>
      exact .cons valueIH environmentIH

theorem EnvironmentHasTypes.reducible
    {environment : Environment} {context : Context}
    (typing : EnvironmentHasTypes environment context) :
    ReducibleEnvironment environment context := by
  cases typing with
  | nil => exact .nil
  | cons valueTyping environmentTyping =>
      exact .cons valueTyping.reducible environmentTyping.reducible
termination_by environment

theorem reducible_environment_evaluates
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {environment : Environment}
    (environmentReducible : ReducibleEnvironment environment context) :
    ∃ value, Evaluates environment expr value := by
  obtain ⟨value, evaluation, _⟩ :=
    reducibility_fundamental typing environmentReducible
  exact ⟨value, evaluation⟩

theorem well_typed_evaluates
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {environment : Environment}
    (environmentTyping : EnvironmentHasTypes environment context) :
    ∃ value, Evaluates environment expr value :=
  reducible_environment_evaluates typing environmentTyping.reducible

theorem closed_well_typed_evaluates
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ value, Evaluates [] expr value :=
  well_typed_evaluates typing .nil

theorem closed_well_typed_run_completes
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ fuel value,
      run fuel (State.initial expr) = .done value ∧
      ValueHasType value type := by
  obtain ⟨value, evaluation⟩ := closed_well_typed_evaluates typing
  obtain ⟨fuel, result⟩ := evaluation_run_complete evaluation
  exact ⟨fuel, value, result, evaluation_preserves_type evaluation typing .nil⟩

theorem closed_well_typed_run_has_sufficient_fuel
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    ∃ required value,
      ValueHasType value type ∧
      ∀ fuel, required ≤ fuel →
        run fuel (State.initial expr) = .done value := by
  obtain ⟨value, evaluation⟩ := closed_well_typed_evaluates typing
  obtain ⟨required, completes⟩ :=
    evaluation_run_complete_with_sufficient_fuel evaluation
  exact ⟨required, value,
    evaluation_preserves_type evaluation typing .nil,
    completes⟩

inductive FrameHasType : Frame → Ty → Ty → Prop where
  | unaryApply
      {op : UnaryOp} :
      FrameHasType (.unaryApply op) op.operandType op.resultType
  | binaryRight
      {op : BinaryOp} {right : Expr} {environment : Environment}
      {context : Context} :
      EnvironmentHasTypes environment context →
      HasType context right op.rightType →
      FrameHasType
        (.binaryRight op right environment)
        op.leftType
        op.resultType
  | binaryApply
      {op : BinaryOp} {leftValue : Value} :
      ValueHasType leftValue op.leftType →
      FrameHasType
        (.binaryApply op leftValue)
        op.rightType
        op.resultType
  | pairRight
      {right : Expr} {environment : Environment} {context : Context}
      {leftType rightType : Ty} :
      EnvironmentHasTypes environment context →
      HasType context right rightType →
      FrameHasType
        (.pairRight right environment)
        leftType
        (.product leftType rightType)
  | pairApply
      {leftValue : Value} {leftType rightType : Ty} :
      ValueHasType leftValue leftType →
      FrameHasType
        (.pairApply leftValue)
        rightType
        (.product leftType rightType)
  | firstApply
      {leftType rightType : Ty} :
      FrameHasType .firstApply (.product leftType rightType) leftType
  | secondApply
      {leftType rightType : Ty} :
      FrameHasType .secondApply (.product leftType rightType) rightType
  | inLeftApply
      {leftType rightType : Ty} :
      FrameHasType
        (.inLeftApply rightType)
        leftType
        (.sum leftType rightType)
  | inRightApply
      {leftType rightType : Ty} :
      FrameHasType
        (.inRightApply leftType)
        rightType
        (.sum leftType rightType)
  | caseBranches
      {leftBranch rightBranch : Expr}
      {environment : Environment} {context : Context}
      {leftType rightType resultType : Ty} :
      EnvironmentHasTypes environment context →
      HasType (leftType :: context) leftBranch resultType →
      HasType (rightType :: context) rightBranch resultType →
      FrameHasType
        (.caseBranches leftBranch rightBranch environment)
        (.sum leftType rightType)
        resultType
  | applyArgument
      {argument : Expr} {environment : Environment} {context : Context}
      {parameterType resultType : Ty} :
      EnvironmentHasTypes environment context →
      HasType context argument parameterType →
      FrameHasType
        (.applyArgument argument environment)
        (.function parameterType resultType)
        resultType
  | applyClosure
      {parameterType resultType : Ty} {body : Expr}
      {environment : Environment} {context : Context} :
      EnvironmentHasTypes environment context →
      HasType (parameterType :: context) body resultType →
      FrameHasType
        (.applyClosure parameterType resultType body environment)
        parameterType
        resultType
  | letBody
      {body : Expr} {environment : Environment} {context : Context}
      {inputType outputType : Ty} :
      EnvironmentHasTypes environment context →
      HasType (inputType :: context) body outputType →
      FrameHasType (.letBody body environment) inputType outputType
  | ifBranches
      {thenBranch elseBranch : Expr} {environment : Environment} {context : Context}
      {outputType : Ty} :
      EnvironmentHasTypes environment context →
      HasType context thenBranch outputType →
      HasType context elseBranch outputType →
      FrameHasType
        (.ifBranches thenBranch elseBranch environment)
        .bool
        outputType

inductive ContinuationHasType : List Frame → Ty → Ty → Prop where
  | nil {type : Ty} :
      ContinuationHasType [] type type
  | cons
      {frame : Frame} {continuation : List Frame}
      {inputType middleType outputType : Ty} :
      FrameHasType frame inputType middleType →
      ContinuationHasType continuation middleType outputType →
      ContinuationHasType (frame :: continuation) inputType outputType

inductive StateHasType : State → Ty → Prop where
  | eval
      {expr : Expr} {environment : Environment} {context : Context}
      {continuation : List Frame} {controlType resultType : Ty} :
      EnvironmentHasTypes environment context →
      HasType context expr controlType →
      ContinuationHasType continuation controlType resultType →
      StateHasType ⟨.eval expr environment, continuation⟩ resultType
  | ret
      {value : Value} {continuation : List Frame} {controlType resultType : Ty} :
      ValueHasType value controlType →
      ContinuationHasType continuation controlType resultType →
      StateHasType ⟨.ret value, continuation⟩ resultType

theorem transition_preserves_state_type
    {state next : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType)
    (transition : Transition state next) :
    StateHasType next resultType := by
  cases transition with
  | unit =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret .unit continuationTyping
  | bool =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret .bool continuationTyping
  | word =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping
          exact .ret .word continuationTyping
  | enterPair =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | pair leftTyping rightTyping =>
              exact .eval
                environmentTyping
                leftTyping
                (.cons
                  (.pairRight environmentTyping rightTyping)
                  continuationTyping)
  | enterPairRight =>
      cases stateTyping with
      | ret leftTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | pairRight environmentTyping rightTyping =>
                  exact .eval
                    environmentTyping
                    rightTyping
                    (.cons (.pairApply leftTyping) restTyping)
  | applyPair =>
      cases stateTyping with
      | ret rightTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | pairApply leftTyping =>
                  exact .ret (.pair leftTyping rightTyping) restTyping
  | enterFirst =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | first operandTyping =>
              exact .eval
                environmentTyping
                operandTyping
                (.cons .firstApply continuationTyping)
  | applyFirst =>
      cases stateTyping with
      | ret pairTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | firstApply =>
                  cases pairTyping with
                  | pair leftTyping rightTyping =>
                      exact .ret leftTyping restTyping
  | enterSecond =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | second operandTyping =>
              exact .eval
                environmentTyping
                operandTyping
                (.cons .secondApply continuationTyping)
  | applySecond =>
      cases stateTyping with
      | ret pairTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | secondApply =>
                  cases pairTyping with
                  | pair leftTyping rightTyping =>
                      exact .ret rightTyping restTyping
  | enterInLeft =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | inLeft payloadTyping =>
              exact .eval
                environmentTyping
                payloadTyping
                (.cons .inLeftApply continuationTyping)
  | applyInLeft =>
      cases stateTyping with
      | ret payloadTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | inLeftApply =>
                  exact .ret (.inLeft payloadTyping) restTyping
  | enterInRight =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | inRight payloadTyping =>
              exact .eval
                environmentTyping
                payloadTyping
                (.cons .inRightApply continuationTyping)
  | applyInRight =>
      cases stateTyping with
      | ret payloadTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | inRightApply =>
                  exact .ret (.inRight payloadTyping) restTyping
  | enterCase =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | caseE scrutineeTyping leftTyping rightTyping =>
              exact .eval
                environmentTyping
                scrutineeTyping
                (.cons
                  (.caseBranches environmentTyping leftTyping rightTyping)
                  continuationTyping)
  | chooseLeft =>
      cases stateTyping with
      | ret sumTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | caseBranches environmentTyping leftTyping rightTyping =>
                  cases sumTyping with
                  | inLeft payloadTyping =>
                      exact .eval
                        (.cons payloadTyping environmentTyping)
                        leftTyping
                        restTyping
  | chooseRight =>
      cases stateTyping with
      | ret sumTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | caseBranches environmentTyping leftTyping rightTyping =>
                  cases sumTyping with
                  | inRight payloadTyping =>
                      exact .eval
                        (.cons payloadTyping environmentTyping)
                        rightTyping
                        restTyping
  | lambda =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | lambda bodyTyping =>
              exact .ret
                (.closure environmentTyping bodyTyping)
                continuationTyping
  | enterApply =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | apply functionTyping argumentTyping =>
              exact .eval
                environmentTyping
                functionTyping
                (.cons
                  (.applyArgument environmentTyping argumentTyping)
                  continuationTyping)
  | beginArgument =>
      cases stateTyping with
      | ret functionTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyArgument callerEnvironmentTyping argumentTyping =>
                  cases functionTyping with
                  | closure capturedEnvironmentTyping bodyTyping =>
                      exact .eval
                        callerEnvironmentTyping
                        argumentTyping
                        (.cons
                          (.applyClosure capturedEnvironmentTyping bodyTyping)
                          restTyping)
  | invokeClosure =>
      cases stateTyping with
      | ret argumentTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | applyClosure capturedEnvironmentTyping bodyTyping =>
                  exact .eval
                    (.cons argumentTyping capturedEnvironmentTyping)
                    bodyTyping
                    restTyping
  | var valueLookup =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | var typeLookup =>
              obtain ⟨found, foundLookup, foundTyping⟩ :=
                environmentTyping.lookup typeLookup
              rw [valueLookup] at foundLookup
              cases foundLookup
              exact .ret foundTyping continuationTyping
  | enterUnary =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | unary operandTyping =>
              exact .eval
                environmentTyping
                operandTyping
                (.cons .unaryApply continuationTyping)
  | applyUnary applied =>
      cases stateTyping with
      | ret operandTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | unaryApply =>
                  exact .ret
                    (unary_apply_result_has_type applied)
                    restTyping
  | enterBinary =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | binary leftTyping rightTyping =>
              exact .eval
                environmentTyping
                leftTyping
                (.cons
                  (.binaryRight environmentTyping rightTyping)
                  continuationTyping)
  | enterBinaryRight =>
      cases stateTyping with
      | ret leftTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | binaryRight environmentTyping rightTyping =>
                  exact .eval
                    environmentTyping
                    rightTyping
                    (.cons (.binaryApply leftTyping) restTyping)
  | applyBinary applied =>
      cases stateTyping with
      | ret rightTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | binaryApply leftTyping =>
                  exact .ret
                    (binary_apply_result_has_type applied)
                    restTyping
  | enterLet =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | letE boundTyping bodyTyping =>
              exact .eval
                environmentTyping
                boundTyping
                (.cons (.letBody environmentTyping bodyTyping) continuationTyping)
  | bindLet =>
      cases stateTyping with
      | ret valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | letBody environmentTyping bodyTyping =>
                  exact .eval
                    (.cons valueTyping environmentTyping)
                    bodyTyping
                    restTyping
  | enterIf =>
      cases stateTyping with
      | eval environmentTyping exprTyping continuationTyping =>
          cases exprTyping with
          | ifE conditionTyping thenTyping elseTyping =>
              exact .eval
                environmentTyping
                conditionTyping
                (.cons
                  (.ifBranches environmentTyping thenTyping elseTyping)
                  continuationTyping)
  | chooseTrue =>
      cases stateTyping with
      | ret valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ifBranches environmentTyping thenTyping elseTyping =>
                  exact .eval environmentTyping thenTyping restTyping
  | chooseFalse =>
      cases stateTyping with
      | ret valueTyping continuationTyping =>
          cases continuationTyping with
          | cons frameTyping restTyping =>
              cases frameTyping with
              | ifBranches environmentTyping thenTyping elseTyping =>
                  exact .eval environmentTyping elseTyping restTyping

theorem state_progress
    {state : State} {resultType : Ty}
    (stateTyping : StateHasType state resultType) :
    (∃ value, state = State.final value) ∨
      ∃ next, Transition state next := by
  cases stateTyping with
  | eval environmentTyping exprTyping continuationTyping =>
      cases exprTyping with
      | unit => exact .inr ⟨_, .unit⟩
      | bool => exact .inr ⟨_, .bool⟩
      | word => exact .inr ⟨_, .word⟩
      | pair => exact .inr ⟨_, .enterPair⟩
      | first => exact .inr ⟨_, .enterFirst⟩
      | second => exact .inr ⟨_, .enterSecond⟩
      | inLeft => exact .inr ⟨_, .enterInLeft⟩
      | inRight => exact .inr ⟨_, .enterInRight⟩
      | caseE => exact .inr ⟨_, .enterCase⟩
      | lambda => exact .inr ⟨_, .lambda⟩
      | apply => exact .inr ⟨_, .enterApply⟩
      | var typeLookup =>
          obtain ⟨value, valueLookup, _⟩ := environmentTyping.lookup typeLookup
          exact .inr ⟨_, .var valueLookup⟩
      | unary =>
          exact .inr ⟨_, .enterUnary⟩
      | binary =>
          exact .inr ⟨_, .enterBinary⟩
      | letE => exact .inr ⟨_, .enterLet⟩
      | ifE => exact .inr ⟨_, .enterIf⟩
  | ret valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact .inl ⟨_, rfl⟩
      | cons frameTyping restTyping =>
          cases frameTyping with
          | unaryApply =>
              obtain ⟨result, applied, _⟩ :=
                UnaryOp.apply_total_of_type
                  _
                  _
                  valueTyping.type_eq
              exact .inr ⟨_, .applyUnary applied⟩
          | binaryRight =>
              exact .inr ⟨_, .enterBinaryRight⟩
          | binaryApply leftTyping =>
              obtain ⟨result, applied, _⟩ :=
                BinaryOp.apply_total_of_types
                  _
                  _
                  _
                  leftTyping.type_eq
                  valueTyping.type_eq
              exact .inr ⟨_, .applyBinary applied⟩
          | pairRight =>
              exact .inr ⟨_, .enterPairRight⟩
          | pairApply =>
              exact .inr ⟨_, .applyPair⟩
          | firstApply =>
              cases valueTyping with
              | pair => exact .inr ⟨_, .applyFirst⟩
          | secondApply =>
              cases valueTyping with
              | pair => exact .inr ⟨_, .applySecond⟩
          | inLeftApply =>
              exact .inr ⟨_, .applyInLeft⟩
          | inRightApply =>
              exact .inr ⟨_, .applyInRight⟩
          | caseBranches =>
              cases valueTyping with
              | inLeft => exact .inr ⟨_, .chooseLeft⟩
              | inRight => exact .inr ⟨_, .chooseRight⟩
          | applyArgument =>
              cases valueTyping with
              | closure => exact .inr ⟨_, .beginArgument⟩
          | applyClosure =>
              exact .inr ⟨_, .invokeClosure⟩
          | letBody =>
              exact .inr ⟨_, .bindLet⟩
          | ifBranches =>
              cases valueTyping with
              | bool =>
                  rename_i decision
                  cases decision with
                  | false => exact .inr ⟨_, .chooseFalse⟩
                  | true => exact .inr ⟨_, .chooseTrue⟩

theorem well_typed_state_never_faults
    {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
    advance state ≠ .fault error := by
  intro faulted
  cases state_progress stateTyping with
  | inl final =>
      obtain ⟨value, stateIsFinal⟩ := final
      subst state
      simp [advance, State.final] at faulted
  | inr progresses =>
      obtain ⟨next, transition⟩ := progresses
      have advances := advance_next_iff.mpr transition
      rw [advances] at faulted
      contradiction

theorem initial_state_has_type
    {expr : Expr} {type : Ty}
    (typing : HasType [] expr type) :
    StateHasType (State.initial expr) type :=
  .eval .nil typing .nil

theorem well_typed_run_never_faults
    {fuel : Nat} {state : State} {resultType : Ty} {error : MachineFault}
    (stateTyping : StateHasType state resultType) :
    run fuel state ≠ .fault error := by
  induction fuel generalizing state with
  | zero =>
      intro faulted
      cases advanced : advance state with
      | done value =>
          rw [run, advanced] at faulted
          contradiction
      | fault actual =>
          exact well_typed_state_never_faults stateTyping advanced
      | next next =>
          rw [run, advanced] at faulted
          contradiction
  | succ fuel fuelIH =>
      intro faulted
      cases advanced : advance state with
      | done value =>
          rw [run, advanced] at faulted
          contradiction
      | fault actual =>
          exact well_typed_state_never_faults stateTyping advanced
      | next next =>
          rw [run, advanced] at faulted
          exact fuelIH
            (transition_preserves_state_type
              stateTyping
              (advance_next_iff.mp advanced))
            faulted

theorem closed_well_typed_run_never_faults
    {fuel : Nat} {expr : Expr} {type : Ty} {error : MachineFault}
    (typing : HasType [] expr type) :
    run fuel (State.initial expr) ≠ .fault error :=
  well_typed_run_never_faults (initial_state_has_type typing)

theorem Program.checked_run_preserves_result_type
    {program : Program} {fuel : Nat} {value : Value}
    (checked : program.check = true)
    (result : program.run fuel = .done value) :
    ValueHasType value program.resultType := by
  have typing := Program.check_sound checked
  have evaluation : Evaluates [] program.body value := by
    exact run_evaluation_sound result
  exact evaluation_preserves_type evaluation typing .nil

theorem Program.checked_run_completes
    {program : Program}
    (checked : program.check = true) :
    ∃ fuel value,
      program.run fuel = .done value ∧
      ValueHasType value program.resultType :=
  closed_well_typed_run_completes (Program.check_sound checked)

theorem Program.checked_run_never_faults
    {program : Program} {fuel : Nat} {error : MachineFault}
    (checked : program.check = true) :
    program.run fuel ≠ .fault error :=
  closed_well_typed_run_never_faults (Program.check_sound checked)

end Solcore.Core
