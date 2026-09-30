import Solcore.Core.LocalSequence

/-! Bare Word compound assignments use an optional payload snapshot captured
before the RHS. Absence is inspected after a successful RHS, so RHS failures
and effects retain their source order. All operations use ordinary Core. -/

set_option autoImplicit false

namespace Solcore.Core.LocalAssignment

inductive Operator where
  | add | subtract | multiply | divide | modulo | bitAnd | bitOr | bitXor
  deriving Repr, BEq, DecidableEq

def Operator.core : Operator → BinaryOp
  | .add => .wordAdd
  | .subtract => .wordSub
  | .multiply => .wordMul
  | .divide => .wordDiv
  | .modulo => .wordMod
  | .bitAnd => .wordAnd
  | .bitOr => .wordOr
  | .bitXor => .wordXor

def Operator.apply : Operator → Word → Word → Word
  | .add => Word.add
  | .subtract => Word.sub
  | .multiply => Word.mul
  | .divide => Word.udiv
  | .modulo => Word.umod
  | .bitAnd => Word.bitAnd
  | .bitOr => Word.bitOr
  | .bitXor => Word.bitXor

theorem Operator.core_apply (operator : Operator) (left right : Word) :
    operator.core.apply (.word left) (.word right) = some (.word (operator.apply left right)) := by
  cases operator <;> rfl

def weakenTwo (expression : Expr) : Expr := (expression.weakenAt 0).weakenAt 0
def weakenThree (expression : Expr) : Expr := (weakenTwo expression).weakenAt 0
def weakenFive (expression : Expr) : Expr := (weakenThree expression).weakenAt 0 |>.weakenAt 0

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
    (.letE (.storeCell (.var 1) (.inRight .unit (.unary .wordNot (.var 0))))
      (weakenThree next)))

private theorem binary_hasType {definitions : DataEnvironment} {context : Context}
    {left right : Expr} (operator : Operator)
    (leftTyped : HasType context left .word definitions)
    (rightTyped : HasType context right .word definitions) :
    HasType context (.binary operator.core left right) .word definitions := by
  cases operator <;> exact .binary leftTyped rightTyped

theorem compound_hasType
    {definitions : DataEnvironment} {context : Context}
    {outputType : Ty} {reference rhs next : Expr} (operator : Operator) (invalidReason : Word)
    (wellFormed : Ty.WellFormed definitions outputType)
    (referenceTyped : HasType context reference (OptionalCell.referenceType .word) definitions)
    (rhsTyped : HasType context rhs (LanguageResult.resultType .word) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (compound outputType operator reference rhs next invalidReason)
      (LanguageResult.resultType outputType) definitions := by
  apply HasType.letE referenceTyped
  apply HasType.letE (.loadCell (.var rfl))
  apply LanguageResult.bind_hasType wellFormed
  · have captured := rhsTyped.weakenAt (inserted := OptionalCell.referenceType .word) 0
    have snapshot := captured.weakenAt (inserted := OptionalCell.cellType .word) 0
    simpa [weakenTwo, Context.insertAt] using snapshot
  · apply HasType.caseE (.var rfl)
    · exact LanguageResult.failure_hasType wellFormed .word
    · apply HasType.letE (.storeCell (.var rfl)
        (.inRight .unit (binary_hasType operator (.var rfl) (.var rfl))))
      have captured := nextTyped.weakenAt (inserted := OptionalCell.referenceType .word) 0
      have snapshot := captured.weakenAt (inserted := OptionalCell.cellType .word) 0
      have right := snapshot.weakenAt (inserted := .word) 0
      have left := right.weakenAt (inserted := .word) 0
      have written := left.weakenAt (inserted := .unit) 0
      simpa [weakenFive, weakenThree, weakenTwo, Context.insertAt] using written

theorem bitNot_hasType
    {definitions : DataEnvironment} {context : Context}
    {outputType : Ty} {reference next : Expr} (invalidReason : Word)
    (wellFormed : Ty.WellFormed definitions outputType)
    (referenceTyped : HasType context reference (OptionalCell.referenceType .word) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (bitNot outputType reference next invalidReason)
      (LanguageResult.resultType outputType) definitions := by
  apply HasType.letE referenceTyped
  apply HasType.caseE (.loadCell (.var rfl))
  · exact LanguageResult.failure_hasType wellFormed .word
  · apply HasType.letE (.storeCell (.var rfl) (.inRight .unit (.unary (.var rfl))))
    have captured := nextTyped.weakenAt (inserted := OptionalCell.referenceType .word) 0
    have operand := captured.weakenAt (inserted := .word) 0
    have written := operand.weakenAt (inserted := .unit) 0
    simpa [weakenThree, weakenTwo, Context.insertAt] using written

theorem compound_rhs_failure
    {environment : Environment} {initialStore referenceStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {snapshot : Value} {reason : Word}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .word) location) referenceStore)
    (readable : referenceStore.read? location = some snapshot)
    (rhsEvaluation : Evaluates
      (snapshot :: .cellRef (OptionalCell.cellType .word) location :: environment)
      referenceStore (weakenTwo rhs) (.inLeft .word (.word reason)) finalStore) :
    Evaluates environment initialStore (compound outputType operator reference rhs next invalidReason)
      (.inLeft outputType (.word reason)) finalStore :=
  .letE referenceEvaluation (.letE (.loadCell (.var rfl) readable)
    (LanguageResult.bind_failure outputType rhsEvaluation))

theorem compound_absent
    {environment : Environment} {initialStore referenceStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {right : Word}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .word) location) referenceStore)
    (absent : referenceStore.read? location = some (.inLeft .word .unit))
    (rhsEvaluation : Evaluates
      (.inLeft .word .unit :: .cellRef (OptionalCell.cellType .word) location :: environment)
      referenceStore (weakenTwo rhs) (.inRight .word (.word right)) finalStore) :
    Evaluates environment initialStore (compound outputType operator reference rhs next invalidReason)
      (.inLeft outputType (.word invalidReason)) finalStore :=
  .letE referenceEvaluation (.letE (.loadCell (.var rfl) absent)
    (LanguageResult.bind_success outputType rhsEvaluation (.caseLeft (.var rfl) (.inLeft .word))))

/-- The write uses the store produced by the RHS, while its operand remains
the earlier snapshot. The continuation sees the actual temporary binders. -/
theorem compound_success
    {environment : Environment}
    {initialStore referenceStore rhsStore writtenStore finalStore : Store}
    {reference rhs next : Expr} {location : Location} {oldValue result : Value} {left right : Word}
    (outputType : Ty) (operator : Operator) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .word) location) referenceStore)
    (snapshotRead : referenceStore.read? location = some (.inRight .unit (.word left)))
    (rhsEvaluation : Evaluates
      (.inRight .unit (.word left) :: .cellRef (OptionalCell.cellType .word) location :: environment)
      referenceStore (weakenTwo rhs) (.inRight .word (.word right)) rhsStore)
    (readable : rhsStore.read? location = some oldValue)
    (written : rhsStore.write? location (.inRight .unit (.word (operator.apply left right))) = some writtenStore)
    (nextEvaluation : Evaluates
      (.unit :: .word left :: .word right :: .inRight .unit (.word left) ::
        .cellRef (OptionalCell.cellType .word) location :: environment)
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
      (.cellRef (OptionalCell.cellType .word) location) referenceStore)
    (absent : referenceStore.read? location = some (.inLeft .word .unit)) :
    Evaluates environment initialStore (bitNot outputType reference next invalidReason)
      (.inLeft outputType (.word invalidReason)) referenceStore :=
  .letE referenceEvaluation (.caseLeft (.loadCell (.var rfl) absent) (.inLeft .word))

theorem bitNot_success
    {environment : Environment} {initialStore referenceStore writtenStore finalStore : Store}
    {reference next : Expr} {location : Location} {value : Word} {result : Value}
    (outputType : Ty) (invalidReason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType .word) location) referenceStore)
    (readable : referenceStore.read? location = some (.inRight .unit (.word value)))
    (written : referenceStore.write? location (.inRight .unit (.word value.bitNot)) = some writtenStore)
    (nextEvaluation : Evaluates
      (.unit :: .word value :: .cellRef (OptionalCell.cellType .word) location :: environment)
      writtenStore (weakenThree next) result finalStore) :
    Evaluates environment initialStore (bitNot outputType reference next invalidReason) result finalStore :=
  .letE referenceEvaluation (.caseRight (.loadCell (.var rfl) readable)
    (.letE (.storeCell (.var rfl) readable (.inRight (.unary (.var rfl) rfl)) written) nextEvaluation))

end Solcore.Core.LocalAssignment
