set_option autoImplicit false

namespace Solcore.Core

def wordModulus : Nat := 2 ^ 256

abbrev Word := Fin wordModulus

namespace Word

def ofNat? (value : Nat) : Option Word :=
  if isLt : value < wordModulus then
    some ⟨value, isLt⟩
  else
    none

def zero : Word := ⟨0, by simp [wordModulus]⟩

end Word

structure DataTypeId where
  index : Nat
  deriving Repr, BEq, DecidableEq

inductive Ty where
  | unit
  | bool
  | word
  | product (left : Ty) (right : Ty)
  | function (parameter : Ty) (result : Ty)
  | sum (left : Ty) (right : Ty)
  | cell (elementType : Ty)
  | namedData (dataType : DataTypeId)
  deriving Repr, BEq, DecidableEq

structure ConstructorId where
  owner : DataTypeId
  index : Nat
  deriving Repr, BEq, DecidableEq

structure DataDefinition where
  constructorPayloadTypes : List Ty
  deriving Repr, BEq, DecidableEq

abbrev DataEnvironment := List DataDefinition

inductive CellPayload : Ty → Prop where
  | unit : CellPayload .unit
  | bool : CellPayload .bool
  | word : CellPayload .word
  | product {left right : Ty} :
      CellPayload left →
      CellPayload right →
      CellPayload (.product left right)
  | sum {left right : Ty} :
      CellPayload left →
      CellPayload right →
      CellPayload (.sum left right)

namespace Ty

def isCellPayload : Ty → Bool
  | .unit
  | .bool
  | .word => true
  | .product left right
  | .sum left right => left.isCellPayload && right.isCellPayload
  | .function _ _
  | .cell _
  | .namedData _ => false

theorem isCellPayload_sound
    {type : Ty}
    (accepted : type.isCellPayload = true) :
    CellPayload type := by
  induction type with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | product left right leftIH rightIH =>
      simp [isCellPayload] at accepted
      exact .product (leftIH accepted.1) (rightIH accepted.2)
  | function parameter result parameterIH resultIH =>
      simp [isCellPayload] at accepted
  | sum left right leftIH rightIH =>
      simp [isCellPayload] at accepted
      exact .sum (leftIH accepted.1) (rightIH accepted.2)
  | cell elementType elementIH =>
      simp [isCellPayload] at accepted
  | namedData dataType =>
      simp [isCellPayload] at accepted

theorem isCellPayload_complete
    {type : Ty}
    (payload : CellPayload type) :
    type.isCellPayload = true := by
  induction payload with
  | unit
  | bool
  | word => rfl
  | product leftPayload rightPayload leftIH rightIH
  | sum leftPayload rightPayload leftIH rightIH =>
      simp [isCellPayload, leftIH, rightIH]

theorem isCellPayload_iff
    {type : Ty} :
    type.isCellPayload = true ↔ CellPayload type :=
  ⟨isCellPayload_sound, isCellPayload_complete⟩

end Ty

inductive UnaryOp where
  | boolNot
  | wordNot
  | wordClz
  deriving Repr, BEq, DecidableEq

namespace UnaryOp

def operandType : UnaryOp → Ty
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

def resultType : UnaryOp → Ty
  | .boolNot => .bool
  | .wordNot
  | .wordClz => .word

end UnaryOp

inductive BinaryOp where
  | wordAdd
  | wordSub
  | wordMul
  | wordDiv
  | wordMod
  | wordEq
  | wordGt
  | wordSgt
  | wordAnd
  | wordOr
  | wordXor
  | wordShl
  | wordShr
  | wordByte
  | wordSar
  | wordPow
  | wordSignExtend
  deriving Repr, BEq, DecidableEq

namespace BinaryOp

def leftType (_ : BinaryOp) : Ty := .word

def rightType (_ : BinaryOp) : Ty := .word

def resultType : BinaryOp → Ty
  | .wordEq
  | .wordGt
  | .wordSgt => .bool
  | .wordAdd
  | .wordSub
  | .wordMul
  | .wordDiv
  | .wordMod
  | .wordAnd
  | .wordOr
  | .wordXor
  | .wordShl
  | .wordShr
  | .wordByte
  | .wordSar
  | .wordPow
  | .wordSignExtend => .word

end BinaryOp

abbrev Location := Nat

inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Word)
  | var (index : Nat)
  | pair (left : Expr) (right : Expr)
  | first (operand : Expr)
  | second (operand : Expr)
  | lambda (parameterType resultType : Ty) (body : Expr)
  | apply (function : Expr) (argument : Expr)
  | inLeft (rightType : Ty) (payload : Expr)
  | inRight (leftType : Ty) (payload : Expr)
  | caseE (scrutinee leftBranch rightBranch : Expr)
  | newCell (elementType : Ty) (initializer : Expr)
  | loadCell (reference : Expr)
  | storeCell (reference value : Expr)
  | construct (constructor : ConstructorId) (payload : Expr)
  | matchData
      (dataType : DataTypeId)
      (resultType : Ty)
      (scrutinee : Expr)
      (branches : List Expr)
  | unary (op : UnaryOp) (operand : Expr)
  | binary (op : BinaryOp) (left : Expr) (right : Expr)
  | letE (value : Expr) (body : Expr)
  | ifE (condition : Expr) (thenBranch : Expr) (elseBranch : Expr)
  deriving Repr

mutual

  def Expr.equal : Expr → Expr → Bool
    | .unit, .unit => true
    | .bool left, .bool right
    | .word left, .word right
    | .var left, .var right => decide (left = right)
    | .pair leftFirst leftSecond, .pair rightFirst rightSecond
    | .apply leftFirst leftSecond, .apply rightFirst rightSecond
    | .storeCell leftFirst leftSecond, .storeCell rightFirst rightSecond
    | .letE leftFirst leftSecond, .letE rightFirst rightSecond =>
        leftFirst.equal rightFirst && leftSecond.equal rightSecond
    | .first left, .first right
    | .second left, .second right
    | .loadCell left, .loadCell right => left.equal right
    | .lambda leftParameter leftResult leftBody,
        .lambda rightParameter rightResult rightBody =>
        decide (leftParameter = rightParameter) &&
          decide (leftResult = rightResult) &&
          leftBody.equal rightBody
    | .inLeft leftType leftPayload, .inLeft rightType rightPayload
    | .inRight leftType leftPayload, .inRight rightType rightPayload
    | .newCell leftType leftPayload, .newCell rightType rightPayload =>
        decide (leftType = rightType) && leftPayload.equal rightPayload
    | .caseE leftScrutinee leftBranch rightBranch,
        .caseE rightScrutinee leftOtherBranch rightOtherBranch
    | .ifE leftScrutinee leftBranch rightBranch,
        .ifE rightScrutinee leftOtherBranch rightOtherBranch =>
        leftScrutinee.equal rightScrutinee &&
          leftBranch.equal leftOtherBranch &&
          rightBranch.equal rightOtherBranch
    | .construct leftConstructor leftPayload,
        .construct rightConstructor rightPayload =>
        decide (leftConstructor = rightConstructor) &&
          leftPayload.equal rightPayload
    | .matchData leftDataType leftResult leftScrutinee leftBranches,
        .matchData rightDataType rightResult rightScrutinee rightBranches =>
        decide (leftDataType = rightDataType) &&
          decide (leftResult = rightResult) &&
          leftScrutinee.equal rightScrutinee &&
          Expr.listEqual leftBranches rightBranches
    | .unary leftOp leftOperand, .unary rightOp rightOperand =>
        decide (leftOp = rightOp) && leftOperand.equal rightOperand
    | .binary leftOp leftLeft leftRight, .binary rightOp rightLeft rightRight =>
        decide (leftOp = rightOp) &&
          leftLeft.equal rightLeft &&
          leftRight.equal rightRight
    | _, _ => false

  def Expr.listEqual : List Expr → List Expr → Bool
    | [], [] => true
    | leftHead :: leftTail, rightHead :: rightTail =>
        leftHead.equal rightHead && Expr.listEqual leftTail rightTail
    | _, _ => false

end

mutual

  theorem Expr.equal_sound
      (left right : Expr)
      (accepted : left.equal right = true) :
      left = right := by
    cases left <;> cases right <;> simp_all [Expr.equal]
    all_goals repeat first | apply And.intro
    all_goals first | apply And.intro | skip
    all_goals first
      | apply Expr.equal_sound <;> simp_all
      | apply Expr.listEqual_sound <;> simp_all
  termination_by sizeOf left

  theorem Expr.listEqual_sound
      (left right : List Expr)
      (accepted : Expr.listEqual left right = true) :
      left = right := by
    cases left <;> cases right <;> simp_all [Expr.listEqual]
    all_goals repeat first | apply And.intro
    all_goals first | apply And.intro | skip
    all_goals first
      | apply Expr.equal_sound <;> simp_all
      | apply Expr.listEqual_sound <;> simp_all
  termination_by sizeOf left

end


mutual

  theorem Expr.equal_self (expr : Expr) : expr.equal expr = true := by
    cases expr <;> simp_all [Expr.equal]
    all_goals repeat first | apply And.intro
    all_goals first | apply And.intro | skip
    all_goals first
      | exact Expr.equal_self _
      | exact Expr.listEqual_self _
  termination_by sizeOf expr

  theorem Expr.listEqual_self (expressions : List Expr) :
      Expr.listEqual expressions expressions = true := by
    cases expressions <;> simp_all [Expr.listEqual]
    all_goals repeat first | apply And.intro
    all_goals first | apply And.intro | skip
    all_goals first
      | exact Expr.equal_self _
      | exact Expr.listEqual_self _
  termination_by sizeOf expressions

end


instance : DecidableEq Expr := fun left right =>
  if accepted : left.equal right then
    isTrue (Expr.equal_sound left right accepted)
  else
    isFalse (fun equality => accepted (by cases equality; exact Expr.equal_self left))

instance : BEq Expr :=
  ⟨fun left right => decide (left = right)⟩

instance : LawfulBEq Expr where
  rfl := by
    intro expr
    change decide (expr = expr) = true
    exact of_decide_eq_self_eq_true expr
  eq_of_beq := by
    intro left right equal
    change decide (left = right) = true at equal
    exact of_decide_eq_true equal

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Word)
  | pair (left : Value) (right : Value)
  | closure
      (parameterType resultType : Ty)
      (body : Expr)
      (environment : List Value)
  | inLeft (rightType : Ty) (payload : Value)
  | inRight (leftType : Ty) (payload : Value)
  | cellRef (elementType : Ty) (location : Location)
  | constructed (constructor : ConstructorId) (payload : Value)
  deriving Repr

mutual

  def Value.decEq (left right : Value) : Decidable (left = right) :=
    match left, right with
    | .unit, .unit => isTrue rfl
    | .bool leftValue, .bool rightValue =>
        if equality : leftValue = rightValue then
          isTrue (by cases equality; rfl)
        else
          isFalse (by
            intro valueEquality
            cases valueEquality
            exact equality rfl)
    | .word leftValue, .word rightValue =>
        if equality : leftValue = rightValue then
          isTrue (by cases equality; rfl)
        else
          isFalse (by
            intro valueEquality
            cases valueEquality
            exact equality rfl)
    | .pair leftFirst leftSecond, .pair rightFirst rightSecond =>
        match Value.decEq leftFirst rightFirst with
        | isFalse notEqual =>
            isFalse (by
              intro pairEquality
              cases pairEquality
              exact notEqual rfl)
        | isTrue firstEquality =>
            match Value.decEq leftSecond rightSecond with
            | isFalse notEqual =>
                isFalse (by
                  intro pairEquality
                  cases pairEquality
                  exact notEqual rfl)
            | isTrue secondEquality =>
                isTrue (by cases firstEquality; cases secondEquality; rfl)
    | .closure leftParameter leftResult leftBody leftEnvironment,
        .closure rightParameter rightResult rightBody rightEnvironment =>
        if parameterEquality : leftParameter = rightParameter then
          if resultEquality : leftResult = rightResult then
            if bodyEquality : leftBody = rightBody then
              match Value.listDecEq leftEnvironment rightEnvironment with
              | isFalse notEqual =>
                  isFalse (by
                    intro closureEquality
                    cases closureEquality
                    exact notEqual rfl)
              | isTrue environmentEquality =>
                  isTrue (by
                    cases parameterEquality
                    cases resultEquality
                    cases bodyEquality
                    cases environmentEquality
                    rfl)
            else
              isFalse (by
                intro closureEquality
                cases closureEquality
                exact bodyEquality rfl)
          else
            isFalse (by
              intro closureEquality
              cases closureEquality
              exact resultEquality rfl)
        else
          isFalse (by
            intro closureEquality
            cases closureEquality
            exact parameterEquality rfl)
    | .inLeft leftRightType leftPayload,
        .inLeft rightRightType rightPayload =>
        if typeEquality : leftRightType = rightRightType then
          match Value.decEq leftPayload rightPayload with
          | isFalse notEqual =>
              isFalse (by
                intro injectionEquality
                cases injectionEquality
                exact notEqual rfl)
          | isTrue payloadEquality =>
              isTrue (by cases typeEquality; cases payloadEquality; rfl)
        else
          isFalse (by
            intro injectionEquality
            cases injectionEquality
            exact typeEquality rfl)
    | .inRight leftLeftType leftPayload,
        .inRight rightLeftType rightPayload =>
        if typeEquality : leftLeftType = rightLeftType then
          match Value.decEq leftPayload rightPayload with
          | isFalse notEqual =>
              isFalse (by
                intro injectionEquality
                cases injectionEquality
                exact notEqual rfl)
          | isTrue payloadEquality =>
              isTrue (by cases typeEquality; cases payloadEquality; rfl)
        else
          isFalse (by
            intro injectionEquality
            cases injectionEquality
            exact typeEquality rfl)
    | .cellRef leftElementType leftLocation,
        .cellRef rightElementType rightLocation =>
        if typeEquality : leftElementType = rightElementType then
          if locationEquality : leftLocation = rightLocation then
            isTrue (by
              cases typeEquality
              cases locationEquality
              rfl)
          else
            isFalse (by
              intro referenceEquality
              cases referenceEquality
              exact locationEquality rfl)
        else
          isFalse (by
            intro referenceEquality
            cases referenceEquality
            exact typeEquality rfl)
    | .constructed leftConstructor leftPayload,
        .constructed rightConstructor rightPayload =>
        if constructorEquality : leftConstructor = rightConstructor then
          match Value.decEq leftPayload rightPayload with
          | isFalse notEqual =>
              isFalse (by
                intro valueEquality
                cases valueEquality
                exact notEqual rfl)
          | isTrue payloadEquality =>
              isTrue (by
                cases constructorEquality
                cases payloadEquality
                rfl)
        else
          isFalse (by
            intro valueEquality
            cases valueEquality
            exact constructorEquality rfl)
    | .unit, .bool _
    | .unit, .word _
    | .unit, .pair _ _
    | .unit, .closure _ _ _ _
    | .unit, .inLeft _ _
    | .unit, .inRight _ _
    | .unit, .cellRef _ _
    | .unit, .constructed _ _
    | .bool _, .unit
    | .bool _, .word _
    | .bool _, .pair _ _
    | .bool _, .closure _ _ _ _
    | .bool _, .inLeft _ _
    | .bool _, .inRight _ _
    | .bool _, .cellRef _ _
    | .bool _, .constructed _ _
    | .word _, .unit
    | .word _, .bool _
    | .word _, .pair _ _
    | .word _, .closure _ _ _ _
    | .word _, .inLeft _ _
    | .word _, .inRight _ _
    | .word _, .cellRef _ _
    | .word _, .constructed _ _
    | .pair _ _, .unit
    | .pair _ _, .bool _
    | .pair _ _, .word _
    | .pair _ _, .closure _ _ _ _
    | .pair _ _, .inLeft _ _
    | .pair _ _, .inRight _ _
    | .pair _ _, .cellRef _ _
    | .pair _ _, .constructed _ _
    | .closure _ _ _ _, .unit
    | .closure _ _ _ _, .bool _
    | .closure _ _ _ _, .word _
    | .closure _ _ _ _, .pair _ _
    | .closure _ _ _ _, .inLeft _ _
    | .closure _ _ _ _, .inRight _ _
    | .closure _ _ _ _, .cellRef _ _
    | .closure _ _ _ _, .constructed _ _
    | .inLeft _ _, .unit
    | .inLeft _ _, .bool _
    | .inLeft _ _, .word _
    | .inLeft _ _, .pair _ _
    | .inLeft _ _, .closure _ _ _ _
    | .inLeft _ _, .inRight _ _
    | .inLeft _ _, .cellRef _ _
    | .inLeft _ _, .constructed _ _
    | .inRight _ _, .unit
    | .inRight _ _, .bool _
    | .inRight _ _, .word _
    | .inRight _ _, .pair _ _
    | .inRight _ _, .closure _ _ _ _
    | .inRight _ _, .inLeft _ _
    | .inRight _ _, .cellRef _ _
    | .inRight _ _, .constructed _ _
    | .cellRef _ _, .unit
    | .cellRef _ _, .bool _
    | .cellRef _ _, .word _
    | .cellRef _ _, .pair _ _
    | .cellRef _ _, .closure _ _ _ _
    | .cellRef _ _, .inLeft _ _
    | .cellRef _ _, .inRight _ _
    | .cellRef _ _, .constructed _ _
    | .constructed _ _, .unit
    | .constructed _ _, .bool _
    | .constructed _ _, .word _
    | .constructed _ _, .pair _ _
    | .constructed _ _, .closure _ _ _ _
    | .constructed _ _, .inLeft _ _
    | .constructed _ _, .inRight _ _
    | .constructed _ _, .cellRef _ _ =>
        isFalse (by intro equality; cases equality)
  termination_by sizeOf left + sizeOf right
  decreasing_by all_goals simp_wf <;> omega

  def Value.listDecEq
      (left right : List Value) : Decidable (left = right) :=
    match left, right with
    | [], [] => isTrue rfl
    | leftHead :: leftTail, rightHead :: rightTail =>
        match Value.decEq leftHead rightHead with
        | isFalse notEqual =>
            isFalse (by
              intro listEquality
              cases listEquality
              exact notEqual rfl)
        | isTrue headEquality =>
            match Value.listDecEq leftTail rightTail with
            | isFalse notEqual =>
                isFalse (by
                  intro listEquality
                  cases listEquality
                  exact notEqual rfl)
            | isTrue tailEquality =>
                isTrue (by cases headEquality; cases tailEquality; rfl)
    | [], _ :: _
    | _ :: _, [] => isFalse (by intro equality; cases equality)
  termination_by sizeOf left + sizeOf right
  decreasing_by all_goals simp_wf <;> omega

end

instance : DecidableEq Value := Value.decEq

instance : BEq Value :=
  ⟨fun left right => decide (left = right)⟩

instance : LawfulBEq Value where
  rfl := by
    intro value
    change decide (value = value) = true
    exact of_decide_eq_self_eq_true value
  eq_of_beq := by
    intro left right equal
    change decide (left = right) = true at equal
    exact of_decide_eq_true equal

def Value.type : Value → Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .pair left right => .product left.type right.type
  | .closure parameterType resultType _ _ =>
      .function parameterType resultType
  | .inLeft rightType payload => .sum payload.type rightType
  | .inRight leftType payload => .sum leftType payload.type
  | .cellRef elementType _ => .cell elementType
  | .constructed constructor _ => .namedData constructor.owner

abbrev Context := List Ty

abbrev Environment := List Value

abbrev Store := List Value

abbrev StoreTyping := List Ty

structure Program where
  resultType : Ty
  body : Expr
  dataDefinitions : DataEnvironment := []
  deriving Repr, BEq, DecidableEq

end Solcore.Core
