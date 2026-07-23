import Solcore.Core.Correspondence

set_option autoImplicit false

namespace Solcore.Core

inductive ValueHasType : Value → Ty → Prop where
  | unit : ValueHasType .unit .unit
  | bool {value : Bool} : ValueHasType (.bool value) .bool
  | word {value : Word} : ValueHasType (.word value) .word

inductive EnvironmentHasTypes : Environment → Context → Prop where
  | nil : EnvironmentHasTypes [] []
  | cons
      {value : Value} {type : Ty} {environment : Environment} {context : Context} :
      ValueHasType value type →
      EnvironmentHasTypes environment context →
      EnvironmentHasTypes (value :: environment) (type :: context)

theorem EnvironmentHasTypes.lookup
    {environment : Environment} {context : Context}
    (hasTypes : EnvironmentHasTypes environment context)
    {index : Nat} {type : Ty}
    (typeLookup : context[index]? = some type) :
    ∃ value, environment[index]? = some value ∧ ValueHasType value type := by
  induction hasTypes generalizing index with
  | nil =>
      simp at typeLookup
  | cons valueTyping tailTyping tailIH =>
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
  cases typing <;> rfl

theorem ValueHasType.of_type_eq
    {value : Value} {type : Ty}
    (typeEquality : value.type = type) :
    ValueHasType value type := by
  cases value <;> simp [Value.type] at typeEquality <;>
    subst type
  · exact .unit
  · exact .bool
  · exact .word

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
          exact ValueHasType.of_type_eq
            (UnaryOp.apply_result_type applied)
  | binary leftEvaluation rightEvaluation applied leftIH rightIH =>
      cases typing with
      | binary leftTyping rightTyping =>
          exact ValueHasType.of_type_eq
            (BinaryOp.apply_result_type applied)
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

theorem well_typed_evaluates
    {context : Context} {expr : Expr} {type : Ty}
    (typing : HasType context expr type)
    {environment : Environment}
    (environmentTyping : EnvironmentHasTypes environment context) :
    ∃ value, Evaluates environment expr value := by
  induction typing generalizing environment with
  | unit => exact ⟨.unit, .unit⟩
  | bool => exact ⟨.bool _, .bool⟩
  | word => exact ⟨.word _, .word⟩
  | var typeLookup =>
      obtain ⟨value, valueLookup, _⟩ := environmentTyping.lookup typeLookup
      exact ⟨value, .var valueLookup⟩
  | unary operandTyping operandIH =>
      obtain ⟨operandValue, operandEvaluation⟩ :=
        operandIH environmentTyping
      have operandValueTyping :=
        evaluation_preserves_type
          operandEvaluation
          operandTyping
          environmentTyping
      obtain ⟨result, applied, _⟩ :=
        UnaryOp.apply_total_of_type
          _
          operandValue
          operandValueTyping.type_eq
      exact ⟨result, .unary operandEvaluation applied⟩
  | binary leftTyping rightTyping leftIH rightIH =>
      obtain ⟨leftValue, leftEvaluation⟩ :=
        leftIH environmentTyping
      obtain ⟨rightValue, rightEvaluation⟩ :=
        rightIH environmentTyping
      have leftValueTyping :=
        evaluation_preserves_type
          leftEvaluation
          leftTyping
          environmentTyping
      have rightValueTyping :=
        evaluation_preserves_type
          rightEvaluation
          rightTyping
          environmentTyping
      obtain ⟨result, applied, _⟩ :=
        BinaryOp.apply_total_of_types
          _
          leftValue
          rightValue
          leftValueTyping.type_eq
          rightValueTyping.type_eq
      exact ⟨result, .binary leftEvaluation rightEvaluation applied⟩
  | letE boundTyping bodyTyping boundIH bodyIH =>
      obtain ⟨boundValue, boundEvaluation⟩ := boundIH environmentTyping
      have boundValueTyping :=
        evaluation_preserves_type boundEvaluation boundTyping environmentTyping
      obtain ⟨result, bodyEvaluation⟩ :=
        bodyIH (.cons boundValueTyping environmentTyping)
      exact ⟨result, .letE boundEvaluation bodyEvaluation⟩
  | ifE conditionTyping thenTyping elseTyping conditionIH thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation⟩ :=
        conditionIH environmentTyping
      have conditionValueTyping :=
        evaluation_preserves_type conditionEvaluation conditionTyping environmentTyping
      obtain ⟨decision, conditionShape⟩ := conditionValueTyping.bool_shape
      subst conditionValue
      cases decision with
      | false =>
          obtain ⟨result, branchEvaluation⟩ := elseIH environmentTyping
          exact ⟨result, .ifFalse conditionEvaluation branchEvaluation⟩
      | true =>
          obtain ⟨result, branchEvaluation⟩ := thenIH environmentTyping
          exact ⟨result, .ifTrue conditionEvaluation branchEvaluation⟩

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
                    (ValueHasType.of_type_eq
                      (UnaryOp.apply_result_type applied))
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
                    (ValueHasType.of_type_eq
                      (BinaryOp.apply_result_type applied))
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
