import Solcore.Core.Eval
import Solcore.Core.Syntax
import Solcore.Core.Typing

/-!
# Laws of the store and of evaluation

Store allocation and writes, determinism of `Evaluates`, store growth, and evaluation of the
cell-free fragment.
-/

section
-- leanmerge: from Solcore.Core.Internal.StoreLaws
set_option autoImplicit false

namespace Solcore.Core

namespace Store

@[simp]
theorem allocate_updatedStore
    (store : Store)
    (value : Value) :
    (store.allocate value).1 = store ++ [value] :=
  rfl

@[simp]
theorem allocate_freshLocation
    (store : Store)
    (value : Value) :
    (store.allocate value).2 = store.length :=
  rfl

@[simp]
theorem allocate_length
    (store : Store)
    (value : Value) :
    (store.allocate value).1.length = store.length + 1 := by
  simp [allocate]

@[simp]
theorem allocate_fresh_lookup
    (store : Store)
    (value : Value) :
    (store.allocate value).1.read? (store.allocate value).2 = some value := by
  simp [allocate, read?]

@[simp]
theorem allocate_fresh_absent
    (store : Store)
    (value : Value) :
    store.read? (store.allocate value).2 = none := by
  simp [allocate, read?]

theorem allocate_old_lookup
    (store : Store)
    (value : Value)
    {location : Location}
    (inBounds : location < store.length) :
    (store.allocate value).1.read? location = store.read? location := by
  simpa [allocate, read?] using
    (List.getElem?_append_left (l₂ := [value]) inBounds)

theorem write?_eq_some_iff
    {store updatedStore : Store}
    {location : Location}
    {value : Value} :
    store.write? location value = some updatedStore ↔
      location < store.length ∧ updatedStore = store.set location value := by
  by_cases inBounds : location < store.length <;>
    simp [write?, inBounds, eq_comm]

theorem write?_success_iff
    (store : Store)
    (location : Location)
    (value : Value) :
    (∃ updatedStore, store.write? location value = some updatedStore) ↔
      location < store.length := by
  constructor
  · rintro ⟨updatedStore, written⟩
    exact (write?_eq_some_iff.mp written).1
  · intro inBounds
    exact ⟨store.set location value,
      write?_eq_some_iff.mpr ⟨inBounds, rfl⟩⟩

@[simp]
theorem write?_failure_iff
    (store : Store)
    (location : Location)
    (value : Value) :
    store.write? location value = none ↔ store.length ≤ location := by
  simp [write?, Nat.not_lt]

theorem write?_preserves_length
    {store updatedStore : Store}
    {location : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore) :
    updatedStore.length = store.length := by
  rw [(write?_eq_some_iff.mp written).2]
  exact List.length_set

theorem write?_reads_written
    {store updatedStore : Store}
    {location : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore) :
    updatedStore.read? location = some value := by
  obtain ⟨inBounds, rfl⟩ := write?_eq_some_iff.mp written
  simp [read?, inBounds]

theorem write?_preserves_other
    {store updatedStore : Store}
    {location otherLocation : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore)
    (different : otherLocation ≠ location) :
    updatedStore.read? otherLocation = store.read? otherLocation := by
  obtain ⟨_, rfl⟩ := write?_eq_some_iff.mp written
  simp [read?, Ne.symm different]

end Store

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.Internal.EvaluationLaws
set_option autoImplicit false

namespace Solcore.Core

theorem evaluation_deterministic
    {environment : Environment} {initialStore : Store} {expr : Expr}
    {left right : Value} {leftStore rightStore : Store}
    (leftEvaluation :
      Evaluates environment initialStore expr left leftStore)
    (rightEvaluation :
      Evaluates environment initialStore expr right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction leftEvaluation generalizing right rightStore with
  | unit =>
      cases rightEvaluation
      exact ⟨rfl, rfl⟩
  | bool =>
      cases rightEvaluation
      exact ⟨rfl, rfl⟩
  | word =>
      cases rightEvaluation
      exact ⟨rfl, rfl⟩
  | integer =>
      cases rightEvaluation
      exact ⟨rfl, rfl⟩
  | pair _ _ leftIH rightIH =>
      cases rightEvaluation with
      | pair otherLeft otherRight =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, rfl⟩ := rightIH otherRight
          exact ⟨rfl, rfl⟩
  | first _ operandIH =>
      cases rightEvaluation with
      | first otherOperand =>
          obtain ⟨pairEquality, storeEquality⟩ := operandIH otherOperand
          cases pairEquality
          exact ⟨rfl, storeEquality⟩
  | second _ operandIH =>
      cases rightEvaluation with
      | second otherOperand =>
          obtain ⟨pairEquality, storeEquality⟩ := operandIH otherOperand
          cases pairEquality
          exact ⟨rfl, storeEquality⟩
  | inLeft _ payloadIH =>
      cases rightEvaluation with
      | inLeft otherPayload =>
          obtain ⟨rfl, rfl⟩ := payloadIH otherPayload
          exact ⟨rfl, rfl⟩
  | inRight _ payloadIH =>
      cases rightEvaluation with
      | inRight otherPayload =>
          obtain ⟨rfl, rfl⟩ := payloadIH otherPayload
          exact ⟨rfl, rfl⟩
  | caseLeft _ _ scrutineeIH branchIH =>
      cases rightEvaluation with
      | caseLeft otherScrutinee otherBranch =>
          obtain ⟨scrutineeEquality, rfl⟩ := scrutineeIH otherScrutinee
          cases scrutineeEquality
          exact branchIH otherBranch
      | caseRight otherScrutinee _ =>
          obtain ⟨impossible, _⟩ := scrutineeIH otherScrutinee
          cases impossible
  | caseRight _ _ scrutineeIH branchIH =>
      cases rightEvaluation with
      | caseLeft otherScrutinee _ =>
          obtain ⟨impossible, _⟩ := scrutineeIH otherScrutinee
          cases impossible
      | caseRight otherScrutinee otherBranch =>
          obtain ⟨scrutineeEquality, rfl⟩ := scrutineeIH otherScrutinee
          cases scrutineeEquality
          exact branchIH otherBranch
  | lambda =>
      cases rightEvaluation
      exact ⟨rfl, rfl⟩
  | apply _ _ _ functionIH argumentIH bodyIH =>
      cases rightEvaluation with
      | apply otherFunction otherArgument otherBody =>
          obtain ⟨functionEquality, rfl⟩ := functionIH otherFunction
          cases functionEquality
          obtain ⟨rfl, rfl⟩ := argumentIH otherArgument
          exact bodyIH otherBody
  | var leftLookup =>
      cases rightEvaluation with
      | var rightLookup =>
          rw [leftLookup] at rightLookup
          cases rightLookup
          exact ⟨rfl, rfl⟩
  | newCell _ initializerIH =>
      cases rightEvaluation with
      | newCell otherInitializer =>
          obtain ⟨rfl, rfl⟩ := initializerIH otherInitializer
          exact ⟨rfl, rfl⟩
  | loadCell _ leftRead referenceIH =>
      cases rightEvaluation with
      | loadCell otherReference rightRead =>
          obtain ⟨referenceEquality, rfl⟩ := referenceIH otherReference
          cases referenceEquality
          rw [leftRead] at rightRead
          cases rightRead
          exact ⟨rfl, rfl⟩
  | storeCell _ leftRead _ leftWrite referenceIH valueIH =>
      cases rightEvaluation with
      | storeCell otherReference rightRead otherValue rightWrite =>
          obtain ⟨referenceEquality, rfl⟩ := referenceIH otherReference
          cases referenceEquality
          rw [leftRead] at rightRead
          cases rightRead
          obtain ⟨rfl, rfl⟩ := valueIH otherValue
          rw [leftWrite] at rightWrite
          cases rightWrite
          exact ⟨rfl, rfl⟩
  | construct _ payloadIH =>
      cases rightEvaluation with
      | construct otherPayload =>
          obtain ⟨rfl, rfl⟩ := payloadIH otherPayload
          exact ⟨rfl, rfl⟩
  | matchData _ _ leftBranchLookup _ scrutineeIH branchIH =>
      cases rightEvaluation with
      | matchData otherScrutinee _ rightBranchLookup otherBranch =>
          obtain ⟨scrutineeEquality, rfl⟩ :=
            scrutineeIH otherScrutinee
          cases scrutineeEquality
          rw [leftBranchLookup] at rightBranchLookup
          cases rightBranchLookup
          exact branchIH otherBranch
  | unary _ leftApplied operandIH =>
      cases rightEvaluation with
      | unary rightOperand rightApplied =>
          obtain ⟨rfl, storeEquality⟩ := operandIH rightOperand
          rw [leftApplied] at rightApplied
          cases rightApplied
          exact ⟨rfl, storeEquality⟩
  | binary _ _ leftApplied leftIH rightIH =>
      cases rightEvaluation with
      | binary otherLeft otherRight rightApplied =>
          obtain ⟨rfl, rfl⟩ := leftIH otherLeft
          obtain ⟨rfl, storeEquality⟩ := rightIH otherRight
          rw [leftApplied] at rightApplied
          cases rightApplied
          exact ⟨rfl, storeEquality⟩
  | ternary _ _ _ leftApplied firstIH secondIH thirdIH =>
      cases rightEvaluation with
      | ternary otherFirst otherSecond otherThird rightApplied =>
          obtain ⟨rfl, rfl⟩ := firstIH otherFirst
          obtain ⟨rfl, rfl⟩ := secondIH otherSecond
          obtain ⟨rfl, storeEquality⟩ := thirdIH otherThird
          rw [leftApplied] at rightApplied
          cases rightApplied
          exact ⟨rfl, storeEquality⟩
  | letE _ _ boundIH bodyIH =>
      cases rightEvaluation with
      | letE rightBound rightBody =>
          obtain ⟨rfl, rfl⟩ := boundIH rightBound
          exact bodyIH rightBody
  | ifTrue _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition rightBranch =>
          obtain ⟨_, rfl⟩ := conditionIH rightCondition
          exact branchIH rightBranch
      | ifFalse rightCondition _ =>
          obtain ⟨impossible, _⟩ := conditionIH rightCondition
          cases impossible
  | ifFalse _ _ conditionIH branchIH =>
      cases rightEvaluation with
      | ifTrue rightCondition _ =>
          obtain ⟨impossible, _⟩ := conditionIH rightCondition
          cases impossible
      | ifFalse rightCondition rightBranch =>
          obtain ⟨_, rfl⟩ := conditionIH rightCondition
          exact branchIH rightBranch

theorem evaluation_store_length_monotone
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation :
      Evaluates environment initialStore expr value finalStore) :
    initialStore.length ≤ finalStore.length := by
  induction evaluation with
  | unit
  | bool
  | word
  | integer
  | lambda
  | var => exact Nat.le_refl _
  | pair _ _ leftIH rightIH =>
      exact Nat.le_trans leftIH rightIH
  | first _ operandIH
  | second _ operandIH
  | inLeft _ operandIH
  | inRight _ operandIH
  | loadCell _ _ operandIH
  | construct _ operandIH
  | unary _ _ operandIH =>
      exact operandIH
  | caseLeft _ _ scrutineeIH branchIH
  | caseRight _ _ scrutineeIH branchIH
  | matchData _ _ _ _ scrutineeIH branchIH
  | letE _ _ scrutineeIH branchIH
  | ifTrue _ _ scrutineeIH branchIH
  | ifFalse _ _ scrutineeIH branchIH =>
      exact Nat.le_trans scrutineeIH branchIH
  | apply _ _ _ functionIH argumentIH bodyIH =>
      exact Nat.le_trans (Nat.le_trans functionIH argumentIH) bodyIH
  | newCell _ initializerIH =>
      exact Nat.le_trans initializerIH (by simp)
  | storeCell _ _ _ written referenceIH valueIH =>
      calc
        _ ≤ _ := referenceIH
        _ ≤ _ := valueIH
        _ = _ := (Store.write?_preserves_length written).symm
  | binary _ _ _ leftIH rightIH =>
      exact Nat.le_trans leftIH rightIH
  | ternary _ _ _ _ firstIH secondIH thirdIH =>
      exact Nat.le_trans (Nat.le_trans firstIH secondIH) thirdIH

/-! ## Cell-free compatibility -/

namespace Expr

/--
`CellFree` identifies the store-passive syntactic fragment: it rejects all
three cell operations and checks every nested function body and branch
structurally. Every frozen Core expression is in this fragment, as are newer
effect-free internal forms such as named-data construction and matching.
-/
inductive CellFree : Expr → Prop where
  | unit : CellFree .unit
  | bool {value : Bool} : CellFree (.bool value)
  | word {value : Word} : CellFree (.word value)
  | integer {value : Int} : CellFree (.integer value)
  | var {index : Nat} : CellFree (.var index)
  | pair {left right : Expr} :
      CellFree left → CellFree right → CellFree (.pair left right)
  | first {operand : Expr} : CellFree operand → CellFree (.first operand)
  | second {operand : Expr} : CellFree operand → CellFree (.second operand)
  | lambda {parameterType resultType : Ty} {body : Expr} :
      CellFree body → CellFree (.lambda parameterType resultType body)
  | apply {function argument : Expr} :
      CellFree function → CellFree argument → CellFree (.apply function argument)
  | inLeft {rightType : Ty} {payload : Expr} :
      CellFree payload → CellFree (.inLeft rightType payload)
  | inRight {leftType : Ty} {payload : Expr} :
      CellFree payload → CellFree (.inRight leftType payload)
  | caseE {scrutinee leftBranch rightBranch : Expr} :
      CellFree scrutinee →
      CellFree leftBranch →
      CellFree rightBranch →
      CellFree (.caseE scrutinee leftBranch rightBranch)
  | construct {constructor : ConstructorId} {payload : Expr} :
      CellFree payload → CellFree (.construct constructor payload)
  | matchData
      {dataType : DataTypeId} {resultType : Ty}
      {scrutinee : Expr} {branches : List Expr} :
      CellFree scrutinee →
      (∀ branch ∈ branches, CellFree branch) →
      CellFree (.matchData dataType resultType scrutinee branches)
  | unary {op : UnaryOp} {operand : Expr} :
      CellFree operand → CellFree (.unary op operand)
  | binary {op : BinaryOp} {left right : Expr} :
      CellFree left → CellFree right → CellFree (.binary op left right)
  | ternary {op : TernaryOp} {first second third : Expr} :
      CellFree first → CellFree second → CellFree third →
      CellFree (.ternary op first second third)
  | letE {value body : Expr} :
      CellFree value → CellFree body → CellFree (.letE value body)
  | ifE {condition thenBranch elseBranch : Expr} :
      CellFree condition →
      CellFree thenBranch →
      CellFree elseBranch →
      CellFree (.ifE condition thenBranch elseBranch)

end Expr

/-
The expression theorem needs a matching invariant for closures supplied by an
environment. A reference value itself is passive: without cell syntax it cannot
read or change the store. A closure is passive only when its body and everything
reachable through its captured environment satisfy the same invariant.
-/
mutual

  inductive StorePassiveValue : Value → Prop where
    | unit : StorePassiveValue .unit
    | bool {value : Bool} : StorePassiveValue (.bool value)
    | word {value : Word} : StorePassiveValue (.word value)
    | integer {value : Int} : StorePassiveValue (.integer value)
    | pair {left right : Value} :
        StorePassiveValue left →
        StorePassiveValue right →
        StorePassiveValue (.pair left right)
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment : Environment} :
        Expr.CellFree body →
        StorePassiveEnvironment environment →
        StorePassiveValue (.closure parameterType resultType body environment)
    | inLeft {rightType : Ty} {payload : Value} :
        StorePassiveValue payload →
        StorePassiveValue (.inLeft rightType payload)
    | inRight {leftType : Ty} {payload : Value} :
        StorePassiveValue payload →
        StorePassiveValue (.inRight leftType payload)
    | cellRef {elementType : Ty} {location : Location} :
        StorePassiveValue (.cellRef elementType location)
    | constructed {constructor : ConstructorId} {payload : Value} :
        StorePassiveValue payload →
        StorePassiveValue (.constructed constructor payload)

  inductive StorePassiveEnvironment : Environment → Prop where
    | nil : StorePassiveEnvironment []
    | cons {value : Value} {environment : Environment} :
        StorePassiveValue value →
        StorePassiveEnvironment environment →
        StorePassiveEnvironment (value :: environment)

end

theorem StorePassiveEnvironment.lookup
    {environment : Environment}
    (passive : StorePassiveEnvironment environment)
    {index : Nat} {value : Value}
    (found : environment[index]? = some value) :
    StorePassiveValue value := by
  induction passive using StorePassiveEnvironment.rec
      (motive_1 := fun _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | closure | inLeft | inRight | cellRef
  | constructed =>
      exact True.intro
  | nil => simp at found
  | cons headPassive _ _ tailIH =>
      cases index with
      | zero =>
          simp at found
          cases found
          exact headPassive
      | succ index =>
          apply tailIH
          simpa using found

private theorem unaryResult_storePassive
    {op : UnaryOp} {operand result : Value}
    (applied : op.apply operand = some result) :
    StorePassiveValue result := by
  have resultType := UnaryOp.apply_result_type applied
  clear applied operand
  cases op <;> cases result <;>
    simp [Value.type, UnaryOp.resultType] at resultType
  all_goals constructor

private theorem binaryResult_storePassive
    {op : BinaryOp} {left right result : Value}
    (applied : op.apply left right = some result) :
    StorePassiveValue result := by
  have resultType := BinaryOp.apply_result_type applied
  clear applied left right
  cases op <;> cases result <;>
    simp [Value.type, BinaryOp.resultType] at resultType
  all_goals constructor

private theorem ternaryResult_storePassive
    {op : TernaryOp} {first second third result : Value}
    (applied : op.apply first second third = some result) :
    StorePassiveValue result := by
  have resultType := TernaryOp.apply_result_type applied
  clear applied first second third
  cases op <;> cases result <;>
    simp [Value.type, TernaryOp.resultType] at resultType
  all_goals constructor

/--
Cell-free evaluation under a passive environment cannot allocate or write: it
returns the exact input store. The returned value remains passive, which makes
the result strong enough to use inductively across function application.
-/
theorem evaluation_preserves_store_of_cellFree
    {environment : Environment} {initialStore finalStore : Store}
    {expr : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (exprFree : Expr.CellFree expr)
    (environmentPassive : StorePassiveEnvironment environment) :
    finalStore = initialStore ∧ StorePassiveValue value := by
  induction evaluation with
  | unit => exact ⟨rfl, .unit⟩
  | bool => exact ⟨rfl, .bool⟩
  | word => exact ⟨rfl, .word⟩
  | integer => exact ⟨rfl, .integer⟩
  | pair _ _ leftIH rightIH =>
      cases exprFree with
      | pair leftFree rightFree =>
          obtain ⟨rfl, leftValuePassive⟩ :=
            leftIH leftFree environmentPassive
          obtain ⟨rfl, rightValuePassive⟩ :=
            rightIH rightFree environmentPassive
          exact ⟨rfl, .pair leftValuePassive rightValuePassive⟩
  | first _ operandIH =>
      cases exprFree with
      | first operandFree =>
          obtain ⟨storeEq, pairPassive⟩ :=
            operandIH operandFree environmentPassive
          cases pairPassive with
          | pair leftPassive _ => exact ⟨storeEq, leftPassive⟩
  | second _ operandIH =>
      cases exprFree with
      | second operandFree =>
          obtain ⟨storeEq, pairPassive⟩ :=
            operandIH operandFree environmentPassive
          cases pairPassive with
          | pair _ rightPassive => exact ⟨storeEq, rightPassive⟩
  | inLeft _ payloadIH =>
      cases exprFree with
      | inLeft payloadFree =>
          obtain ⟨storeEq, valuePassive⟩ :=
            payloadIH payloadFree environmentPassive
          exact ⟨storeEq, .inLeft valuePassive⟩
  | inRight _ payloadIH =>
      cases exprFree with
      | inRight payloadFree =>
          obtain ⟨storeEq, valuePassive⟩ :=
            payloadIH payloadFree environmentPassive
          exact ⟨storeEq, .inRight valuePassive⟩
  | caseLeft _ _ scrutineeIH branchIH =>
      cases exprFree with
      | caseE scrutineeFree leftFree _ =>
          obtain ⟨rfl, injectionPassive⟩ :=
            scrutineeIH scrutineeFree environmentPassive
          cases injectionPassive with
          | inLeft payloadPassive =>
              exact branchIH leftFree
                (.cons payloadPassive environmentPassive)
  | caseRight _ _ scrutineeIH branchIH =>
      cases exprFree with
      | caseE scrutineeFree _ rightFree =>
          obtain ⟨rfl, injectionPassive⟩ :=
            scrutineeIH scrutineeFree environmentPassive
          cases injectionPassive with
          | inRight payloadPassive =>
              exact branchIH rightFree
                (.cons payloadPassive environmentPassive)
  | lambda =>
      cases exprFree with
      | lambda bodyFree =>
          exact ⟨rfl, .closure bodyFree environmentPassive⟩
  | apply _ _ _ functionIH argumentIH bodyIH =>
      cases exprFree with
      | apply functionFree argumentFree =>
          obtain ⟨rfl, functionValuePassive⟩ :=
            functionIH functionFree environmentPassive
          cases functionValuePassive with
          | closure bodyFree capturedEnvironmentPassive =>
              obtain ⟨rfl, argumentValuePassive⟩ :=
                argumentIH argumentFree environmentPassive
              exact bodyIH bodyFree
                (.cons argumentValuePassive capturedEnvironmentPassive)
  | var found =>
      exact ⟨rfl, environmentPassive.lookup found⟩
  | newCell => cases exprFree
  | loadCell => cases exprFree
  | storeCell => cases exprFree
  | construct _ payloadIH =>
      cases exprFree with
      | construct payloadFree =>
          obtain ⟨storeEq, payloadPassive⟩ :=
            payloadIH payloadFree environmentPassive
          exact ⟨storeEq, .constructed payloadPassive⟩
  | matchData _ _ branchLookup _ scrutineeIH branchIH =>
      cases exprFree with
      | matchData scrutineeFree branchesFree =>
          obtain ⟨rfl, scrutineePassive⟩ :=
            scrutineeIH scrutineeFree environmentPassive
          cases scrutineePassive with
          | constructed payloadPassive =>
              exact branchIH
                (branchesFree _ (List.mem_of_getElem? branchLookup))
                (.cons payloadPassive environmentPassive)
  | unary _ applied operandIH =>
      cases exprFree with
      | unary operandFree =>
          obtain ⟨storeEq, _⟩ := operandIH operandFree environmentPassive
          exact ⟨storeEq, unaryResult_storePassive applied⟩
  | binary _ _ applied leftIH rightIH =>
      cases exprFree with
      | binary leftFree rightFree =>
          obtain ⟨rfl, _⟩ := leftIH leftFree environmentPassive
          obtain ⟨storeEq, _⟩ := rightIH rightFree environmentPassive
          exact ⟨storeEq, binaryResult_storePassive applied⟩
  | ternary _ _ _ applied firstIH secondIH thirdIH =>
      cases exprFree with
      | ternary firstFree secondFree thirdFree =>
          obtain ⟨rfl, _⟩ := firstIH firstFree environmentPassive
          obtain ⟨rfl, _⟩ := secondIH secondFree environmentPassive
          obtain ⟨storeEq, _⟩ := thirdIH thirdFree environmentPassive
          exact ⟨storeEq, ternaryResult_storePassive applied⟩
  | letE _ _ valueIH bodyIH =>
      cases exprFree with
      | letE valueFree bodyFree =>
          obtain ⟨rfl, boundValuePassive⟩ :=
            valueIH valueFree environmentPassive
          exact bodyIH bodyFree (.cons boundValuePassive environmentPassive)
  | ifTrue _ _ conditionIH branchIH =>
      cases exprFree with
      | ifE conditionFree thenFree _ =>
          obtain ⟨rfl, _⟩ := conditionIH conditionFree environmentPassive
          exact branchIH thenFree environmentPassive
  | ifFalse _ _ conditionIH branchIH =>
      cases exprFree with
      | ifE conditionFree _ elseFree =>
          obtain ⟨rfl, _⟩ := conditionIH conditionFree environmentPassive
          exact branchIH elseFree environmentPassive

/-- A cell-free expression evaluated in the empty environment preserves any store. -/
theorem evaluation_preserves_store_of_closed_cellFree
    {initialStore finalStore : Store} {expr : Expr} {value : Value}
    (evaluation : Evaluates [] initialStore expr value finalStore)
    (exprFree : Expr.CellFree expr) :
    finalStore = initialStore :=
  (evaluation_preserves_store_of_cellFree evaluation exprFree .nil).1

/-- Frozen Core execution from the empty store also ends with the empty store. -/
theorem evaluation_ends_with_empty_store_of_closed_cellFree
    {expr : Expr} {value : Value} {finalStore : Store}
    (evaluation : Evaluates [] [] expr value finalStore)
    (exprFree : Expr.CellFree expr) :
    finalStore = [] :=
  evaluation_preserves_store_of_closed_cellFree evaluation exprFree

end Solcore.Core
end
