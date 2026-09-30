import Solcore.Core.LocalAssignment
import Solcore.Core.IntegerPrimitives

/-! Bare Integer compound assignments use an optional payload snapshot captured
before the RHS. Absence is inspected after a successful RHS, so RHS failures
and effects retain their source order. All operations use ordinary Core. -/

set_option autoImplicit false

namespace Solcore.Core.IntegerAssignment

inductive Operator where
  | add | subtract | multiply | divide | modulo | bitAnd | bitOr | bitXor
  deriving Repr, BEq, DecidableEq

def Operator.core : Operator → BinaryOp
  | .add => .integerAdd
  | .subtract => .integerSub
  | .multiply => .integerMul
  | .divide => .integerDiv
  | .modulo => .integerMod
  | .bitAnd => .integerAnd
  | .bitOr => .integerOr
  | .bitXor => .integerXor

def Operator.apply : Operator → Int → Int → Int
  | .add => fun left right => left + right
  | .subtract => fun left right => left - right
  | .multiply => fun left right => left * right
  | .divide => Integer.divide
  | .modulo => Integer.modulo
  | .bitAnd => Integer.bitAnd
  | .bitOr => Integer.bitOr
  | .bitXor => Integer.bitXor

theorem Operator.core_apply (operator : Operator) (left right : Int) :
    operator.core.apply (.integer left) (.integer right) = some (.integer (operator.apply left right)) := by
  cases operator <;> rfl

abbrev weakenTwo := LocalAssignment.weakenTwo
abbrev weakenThree := LocalAssignment.weakenThree
abbrev weakenFive := LocalAssignment.weakenFive

/-- Save the raw optional marker first. Only a successful RHS inspects it,
writes the arithmetic result, and runs the lexical continuation. -/
def compound (outputType : Ty) (operator : Operator) (reference rhs next : Expr)
    (invalidReason : Word) : Expr :=
  .letE reference (.letE (.loadCell (.var 0))
    (LanguageResult.bind outputType (weakenTwo rhs)
      (.caseE (.var 1) (LanguageResult.failure outputType (.word invalidReason))
        (.letE (.storeCell (.var 3)
          (.inRight .unit (.binary operator.core (.var 0) (.var 1)))) (weakenFive next)))))

/-- Unary assignment has no RHS, so its snapshot is inspected immediately. -/
def bitNot (outputType : Ty) (reference next : Expr) (invalidReason : Word) : Expr :=
  .letE reference (.caseE (.loadCell (.var 0))
    (LanguageResult.failure outputType (.word invalidReason))
    (.letE (.storeCell (.var 1) (.inRight .unit (.unary .integerNot (.var 0))))
      (weakenThree next)))

private theorem binary_hasType {definitions : DataEnvironment} {context : Context}
    {left right : Expr} (operator : Operator)
    (leftTyped : HasType context left .integer definitions)
    (rightTyped : HasType context right .integer definitions) :
    HasType context (.binary operator.core left right) .integer definitions := by
  cases operator <;> exact .binary leftTyped rightTyped

theorem compound_hasType
    {definitions : DataEnvironment} {context : Context}
    {outputType : Ty} {reference rhs next : Expr} (operator : Operator) (invalidReason : Word)
    (wellFormed : Ty.WellFormed definitions outputType)
    (referenceTyped : HasType context reference (OptionalCell.referenceType .integer) definitions)
    (rhsTyped : HasType context rhs (LanguageResult.resultType .integer) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (compound outputType operator reference rhs next invalidReason)
      (LanguageResult.resultType outputType) definitions := by
  apply HasType.letE referenceTyped
  apply HasType.letE (.loadCell (.var rfl))
  apply LanguageResult.bind_hasType wellFormed
  · have captured := rhsTyped.weakenAt (inserted := OptionalCell.referenceType .integer) 0
    have snapshot := captured.weakenAt (inserted := OptionalCell.cellType .integer) 0
    simpa [weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree, LocalAssignment.weakenFive, Context.insertAt] using snapshot
  · apply HasType.caseE (.var rfl)
    · exact LanguageResult.failure_hasType wellFormed .word
    · apply HasType.letE (.storeCell (.var rfl)
        (.inRight .unit (binary_hasType operator (.var rfl) (.var rfl))))
      have captured := nextTyped.weakenAt (inserted := OptionalCell.referenceType .integer) 0
      have snapshot := captured.weakenAt (inserted := OptionalCell.cellType .integer) 0
      have right := snapshot.weakenAt (inserted := .integer) 0
      have left := right.weakenAt (inserted := .integer) 0
      have written := left.weakenAt (inserted := .unit) 0
      simpa [weakenFive, weakenThree, weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree, LocalAssignment.weakenFive, Context.insertAt] using written

theorem bitNot_hasType
    {definitions : DataEnvironment} {context : Context}
    {outputType : Ty} {reference next : Expr} (invalidReason : Word)
    (wellFormed : Ty.WellFormed definitions outputType)
    (referenceTyped : HasType context reference (OptionalCell.referenceType .integer) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (bitNot outputType reference next invalidReason)
      (LanguageResult.resultType outputType) definitions := by
  apply HasType.letE referenceTyped
  apply HasType.caseE (.loadCell (.var rfl))
  · exact LanguageResult.failure_hasType wellFormed .word
  · apply HasType.letE (.storeCell (.var rfl) (.inRight .unit (.unary (.var rfl))))
    have captured := nextTyped.weakenAt (inserted := OptionalCell.referenceType .integer) 0
    have operand := captured.weakenAt (inserted := .integer) 0
    have written := operand.weakenAt (inserted := .unit) 0
    simpa [weakenThree, weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree, LocalAssignment.weakenFive, Context.insertAt] using written

theorem compound_rhs_failure
    {environment : Environment} {initialStore referenceStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {snapshot : Value} {reason : Word}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .integer) location) referenceStore)
    (readable : referenceStore.read? location = some snapshot)
    (rhsEvaluation : Evaluates
      (snapshot :: .cellRef (OptionalCell.cellType .integer) location :: environment)
      referenceStore (weakenTwo rhs) (.inLeft .integer (.word reason)) finalStore) :
    Evaluates environment initialStore (compound outputType operator reference rhs next invalidReason)
      (.inLeft outputType (.word reason)) finalStore :=
  .letE referenceEvaluation (.letE (.loadCell (.var rfl) readable)
    (LanguageResult.bind_failure outputType rhsEvaluation))

theorem compound_absent
    {environment : Environment} {initialStore referenceStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {right : Int}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .integer) location) referenceStore)
    (absent : referenceStore.read? location = some (.inLeft .integer .unit))
    (rhsEvaluation : Evaluates
      (.inLeft .integer .unit :: .cellRef (OptionalCell.cellType .integer) location :: environment)
      referenceStore (weakenTwo rhs) (.inRight .word (.integer right)) finalStore) :
    Evaluates environment initialStore (compound outputType operator reference rhs next invalidReason)
      (.inLeft outputType (.word invalidReason)) finalStore :=
  .letE referenceEvaluation (.letE (.loadCell (.var rfl) absent)
    (LanguageResult.bind_success outputType rhsEvaluation (.caseLeft (.var rfl) (.inLeft .word))))

/-- The write uses the store produced by the RHS, while its operand remains
the earlier snapshot. The continuation sees the actual temporary binders. -/
theorem compound_success
    {environment : Environment}
    {initialStore referenceStore rhsStore writtenStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {oldValue result : Value} {left right : Int}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .integer) location) referenceStore)
    (snapshotRead : referenceStore.read? location = some (.inRight .unit (.integer left)))
    (rhsEvaluation : Evaluates
      (.inRight .unit (.integer left) :: .cellRef (OptionalCell.cellType .integer) location :: environment)
      referenceStore (weakenTwo rhs) (.inRight .word (.integer right)) rhsStore)
    (readable : rhsStore.read? location = some oldValue)
    (written : rhsStore.write? location (.inRight .unit (.integer (operator.apply left right))) = some writtenStore)
    (nextEvaluation : Evaluates
      (.unit :: .integer left :: .integer right :: .inRight .unit (.integer left) ::
        .cellRef (OptionalCell.cellType .integer) location :: environment)
      writtenStore (weakenFive next) result finalStore) :
    Evaluates environment initialStore (compound outputType operator reference rhs next invalidReason)
      result finalStore :=
  .letE referenceEvaluation (.letE (.loadCell (.var rfl) snapshotRead)
    (LanguageResult.bind_success outputType rhsEvaluation (.caseRight (.var rfl)
      (.letE (.storeCell (.var rfl) readable
        (.inRight (.binary (.var rfl) (.var rfl) (operator.core_apply left right))) written)
        nextEvaluation))))

theorem bitNot_absent
    {environment : Environment} {initialStore referenceStore : Store}
    {reference next : Expr} {location : Location} (outputType : Ty) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .integer) location) referenceStore)
    (absent : referenceStore.read? location = some (.inLeft .integer .unit)) :
    Evaluates environment initialStore (bitNot outputType reference next invalidReason)
      (.inLeft outputType (.word invalidReason)) referenceStore :=
  .letE referenceEvaluation (.caseLeft (.loadCell (.var rfl) absent) (.inLeft .word))

theorem bitNot_success
    {environment : Environment} {initialStore referenceStore writtenStore finalStore : Store}
    {reference next : Expr} {location : Location} {value : Int} {result : Value}
    (outputType : Ty) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .integer) location) referenceStore)
    (readable : referenceStore.read? location = some (.inRight .unit (.integer value)))
    (written : referenceStore.write? location (.inRight .unit (.integer (Int.not value))) = some writtenStore)
    (nextEvaluation : Evaluates
      (.unit :: .integer value :: .cellRef (OptionalCell.cellType .integer) location :: environment)
      writtenStore (weakenThree next) result finalStore) :
    Evaluates environment initialStore (bitNot outputType reference next invalidReason) result finalStore :=
  .letE referenceEvaluation (.caseRight (.loadCell (.var rfl) readable)
    (.letE (.storeCell (.var rfl) readable (.inRight (.unary (.var rfl) rfl)) written) nextEvaluation))

end Solcore.Core.IntegerAssignment
