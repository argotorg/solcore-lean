import Solcore.Core.OptionalCell
import Solcore.Core.Renaming

/-! Local statement sequencing uses ordinary Core sums and cells. Continuations
are lowered in their lexical cell context before temporary result binders are
inserted. Evaluation laws use those actual inserted environments explicitly. -/

set_option autoImplicit false

namespace Solcore.Core.LocalSequence

def discard (outputType : Ty) (computation next : Expr) : Expr :=
  LanguageResult.bind outputType computation (next.weakenAt 0)

/-- `body` is lowered under the new cell reference followed by its outer scope. -/
def letUninitialized (payloadType : Ty) (body : Expr) : Expr :=
  .letE (OptionalCell.allocate payloadType) body

/-- The initializer's successful payload is inserted after the new reference. -/
def letInitialized (outputType payloadType : Ty) (initializer body : Expr) : Expr :=
  LanguageResult.bind outputType initializer
    (.letE (OptionalCell.allocateInitialized payloadType (.var 0)) (body.weakenAt 1))

/-- Capture the target reference before evaluating the RHS. Only success writes
the initialized payload and evaluates the lexical continuation. -/
def assign (outputType : Ty) (reference rhs next : Expr) : Expr :=
  .letE reference
    (LanguageResult.bind outputType (rhs.weakenAt 0)
      (.letE (.storeCell (.var 1) (.inRight .unit (.var 0)))
        (((next.weakenAt 0).weakenAt 0).weakenAt 0)))

/-- Evaluate tuple elements from left to right, carrying their shared store. -/
def pair (leftType rightType : Ty) (left right : Expr) : Expr :=
  LanguageResult.bind (.product leftType rightType) left
    (LanguageResult.bind (.product leftType rightType) (right.weakenAt 0)
      (LanguageResult.success (.pair (.var 1) (.var 0))))

theorem discard_hasType
    {definitions : DataEnvironment} {context : Context}
    {inputType outputType : Ty} {computation next : Expr}
    (wellFormed : Ty.WellFormed definitions outputType)
    (computationTyped : HasType context computation (LanguageResult.resultType inputType) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (discard outputType computation next)
      (LanguageResult.resultType outputType) definitions := by
  apply LanguageResult.bind_hasType wellFormed computationTyped
  simpa [Context.insertAt] using nextTyped.weakenAt (inserted := inputType) 0

theorem letUninitialized_hasType
    {definitions : DataEnvironment} {context : Context}
    {payloadType outputType : Ty} {body : Expr}
    (wellFormed : Ty.WellFormed definitions payloadType)
    (bodyTyped : HasType (OptionalCell.referenceType payloadType :: context) body
      (LanguageResult.resultType outputType) definitions) :
    HasType context (letUninitialized payloadType body)
      (LanguageResult.resultType outputType) definitions :=
  .letE (OptionalCell.allocate_hasType wellFormed) bodyTyped

theorem letInitialized_hasType
    {definitions : DataEnvironment} {context : Context}
    {payloadType outputType : Ty} {initializer body : Expr}
    (wellFormed : Ty.WellFormed definitions outputType)
    (initializerTyped : HasType context initializer (LanguageResult.resultType payloadType) definitions)
    (bodyTyped : HasType (OptionalCell.referenceType payloadType :: context) body
      (LanguageResult.resultType outputType) definitions) :
    HasType context (letInitialized outputType payloadType initializer body)
      (LanguageResult.resultType outputType) definitions := by
  apply LanguageResult.bind_hasType wellFormed initializerTyped
  apply HasType.letE (OptionalCell.allocateInitialized_hasType (.var rfl))
  simpa [Context.insertAt] using bodyTyped.weakenAt (inserted := payloadType) 1

theorem assign_hasType
    {definitions : DataEnvironment} {context : Context}
    {payloadType outputType : Ty} {reference rhs next : Expr}
    (wellFormed : Ty.WellFormed definitions outputType)
    (referenceTyped : HasType context reference (OptionalCell.referenceType payloadType) definitions)
    (rhsTyped : HasType context rhs (LanguageResult.resultType payloadType) definitions)
    (nextTyped : HasType context next (LanguageResult.resultType outputType) definitions) :
    HasType context (assign outputType reference rhs next)
      (LanguageResult.resultType outputType) definitions := by
  apply HasType.letE referenceTyped
  apply LanguageResult.bind_hasType wellFormed
  · simpa [Context.insertAt] using
      rhsTyped.weakenAt (inserted := OptionalCell.referenceType payloadType) 0
  · apply HasType.letE (.storeCell (.var rfl) (.inRight .unit (.var rfl)))
    have capturedNext := nextTyped.weakenAt (inserted := OptionalCell.referenceType payloadType) 0
    have payloadNext := HasType.weakenAt (inserted := payloadType) capturedNext 0
    have writtenNext := HasType.weakenAt (inserted := .unit) payloadNext 0
    simpa [Context.insertAt] using writtenNext

theorem pair_hasType
    {definitions : DataEnvironment} {context : Context}
    {leftType rightType : Ty} {left right : Expr}
    (leftWellFormed : Ty.WellFormed definitions leftType)
    (rightWellFormed : Ty.WellFormed definitions rightType)
    (leftTyped : HasType context left (LanguageResult.resultType leftType) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType rightType) definitions) :
    HasType context (pair leftType rightType left right)
      (LanguageResult.resultType (.product leftType rightType)) definitions := by
  apply LanguageResult.bind_hasType (.product leftWellFormed rightWellFormed) leftTyped
  apply LanguageResult.bind_hasType (.product leftWellFormed rightWellFormed)
  · simpa [Context.insertAt] using rightTyped.weakenAt (inserted := leftType) 0
  · exact LanguageResult.success_hasType (.pair (.var rfl) (.var rfl))

theorem discard_failure
    {environment : Environment} {initialStore finalStore : Store}
    {inputType : Ty} {computation next : Expr} {reason : Word} (outputType : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft inputType (.word reason)) finalStore) :
    Evaluates environment initialStore (discard outputType computation next)
      (.inLeft outputType (.word reason)) finalStore :=
  LanguageResult.bind_failure outputType evaluation

theorem discard_success
    {environment : Environment} {initialStore nextStore finalStore : Store}
    {computation next : Expr} {payload result : Value} (outputType : Ty)
    (computationEvaluation : Evaluates environment initialStore computation
      (.inRight .word payload) nextStore)
    (nextEvaluation : Evaluates (payload :: environment) nextStore
      (next.weakenAt 0) result finalStore) :
    Evaluates environment initialStore (discard outputType computation next) result finalStore :=
  LanguageResult.bind_success outputType computationEvaluation nextEvaluation

theorem letUninitialized_evaluates
    {environment : Environment} {initialStore finalStore : Store}
    {body : Expr} {result : Value} (payloadType : Ty)
    (bodyEvaluation : Evaluates
      (.cellRef (OptionalCell.cellType payloadType) initialStore.length :: environment)
      (initialStore ++ [.inLeft payloadType .unit]) body result finalStore) :
    Evaluates environment initialStore (letUninitialized payloadType body) result finalStore :=
  .letE (OptionalCell.allocate_evaluates payloadType environment initialStore) bodyEvaluation

theorem letInitialized_failure
    {environment : Environment} {initialStore finalStore : Store}
    {initializer body : Expr} {reason : Word} (outputType payloadType : Ty)
    (evaluation : Evaluates environment initialStore initializer
      (.inLeft payloadType (.word reason)) finalStore) :
    Evaluates environment initialStore (letInitialized outputType payloadType initializer body)
      (.inLeft outputType (.word reason)) finalStore :=
  LanguageResult.bind_failure outputType evaluation

/-- Initializer effects precede allocation. The body receives the new reference
at index zero and the initializer payload at index one. -/
theorem letInitialized_success
    {environment : Environment} {initialStore initializedStore finalStore : Store}
    {initializer body : Expr} {value result : Value} (outputType payloadType : Ty)
    (initializerEvaluation : Evaluates environment initialStore initializer
      (.inRight .word value) initializedStore)
    (bodyEvaluation : Evaluates
      (.cellRef (OptionalCell.cellType payloadType) initializedStore.length :: value :: environment)
      (initializedStore ++ [.inRight .unit value]) (body.weakenAt 1) result finalStore) :
    Evaluates environment initialStore (letInitialized outputType payloadType initializer body)
      result finalStore :=
  LanguageResult.bind_success outputType initializerEvaluation
    (.letE (OptionalCell.allocateInitialized_evaluates (.var rfl)) bodyEvaluation)

theorem assign_failure
    {environment : Environment} {initialStore referenceStore finalStore : Store}
    {reference rhs next : Expr} {payloadType : Ty} {location : Location} {reason : Word}
    (outputType : Ty)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType payloadType) location) referenceStore)
    (rhsEvaluation : Evaluates
      (.cellRef (OptionalCell.cellType payloadType) location :: environment)
      referenceStore (rhs.weakenAt 0) (.inLeft payloadType (.word reason)) finalStore) :
    Evaluates environment initialStore (assign outputType reference rhs next)
      (.inLeft outputType (.word reason)) finalStore :=
  .letE referenceEvaluation (LanguageResult.bind_failure outputType rhsEvaluation)

theorem assign_success
    {environment : Environment}
    {initialStore referenceStore rhsStore writtenStore finalStore : Store}
    {reference rhs next : Expr} {payloadType : Ty} {location : Location}
    {oldValue value result : Value} (outputType : Ty)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType payloadType) location) referenceStore)
    (rhsEvaluation : Evaluates
      (.cellRef (OptionalCell.cellType payloadType) location :: environment)
      referenceStore (rhs.weakenAt 0) (.inRight .word value) rhsStore)
    (readable : rhsStore.read? location = some oldValue)
    (written : rhsStore.write? location (.inRight .unit value) = some writtenStore)
    (nextEvaluation : Evaluates
      (.unit :: value :: .cellRef (OptionalCell.cellType payloadType) location :: environment)
      writtenStore (((next.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (assign outputType reference rhs next) result finalStore :=
  .letE referenceEvaluation (LanguageResult.bind_success outputType rhsEvaluation
    (.letE (.storeCell (.var rfl) readable (.inRight (.var rfl)) written) nextEvaluation))

theorem pair_left_failure
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr} {reason : Word} (leftType rightType : Ty)
    (evaluation : Evaluates environment initialStore left
      (.inLeft leftType (.word reason)) finalStore) :
    Evaluates environment initialStore (pair leftType rightType left right)
      (.inLeft (.product leftType rightType) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem pair_right_failure
    {environment : Environment} {initialStore rightStore finalStore : Store}
    {left right : Expr} {leftValue : Value} {reason : Word} (leftType rightType : Ty)
    (leftEvaluation : Evaluates environment initialStore left (.inRight .word leftValue) rightStore)
    (rightEvaluation : Evaluates (leftValue :: environment) rightStore (right.weakenAt 0)
      (.inLeft rightType (.word reason)) finalStore) :
    Evaluates environment initialStore (pair leftType rightType left right)
      (.inLeft (.product leftType rightType) (.word reason)) finalStore :=
  LanguageResult.bind_success _ leftEvaluation (LanguageResult.bind_failure _ rightEvaluation)

theorem pair_success
    {environment : Environment} {initialStore rightStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Value} (leftType rightType : Ty)
    (leftEvaluation : Evaluates environment initialStore left (.inRight .word leftValue) rightStore)
    (rightEvaluation : Evaluates (leftValue :: environment) rightStore (right.weakenAt 0)
      (.inRight .word rightValue) finalStore) :
    Evaluates environment initialStore (pair leftType rightType left right)
      (.inRight .word (.pair leftValue rightValue)) finalStore :=
  LanguageResult.bind_success _ leftEvaluation (LanguageResult.bind_success _ rightEvaluation
    (.inRight (.pair (.var rfl) (.var rfl))))

end Solcore.Core.LocalSequence
