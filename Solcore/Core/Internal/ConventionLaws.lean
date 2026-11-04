import Solcore.Core.Conventions
import Solcore.Core.LanguageResult
import Solcore.Core.Internal.EvaluationLaws
import Solcore.Core.Internal.Renaming
import Solcore.Core.Primitive

/-!
# Laws of the conventions

Typing and evaluation laws of `Conventions`, one section per convention. The evaluation laws name
every binder a convention inserts and the store it shares.
-/

section
-- leanmerge: from Solcore.Core.OptionalCell
/-! Mutable source bindings use ordinary Core cells with an explicit optional
payload. An absent value becomes a language failure on read. References and
closures keep the same shared store as ordinary Core values. -/

set_option autoImplicit false

namespace Solcore.Core.OptionalCell

theorem allocate_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) :
    HasType context (allocate type) (referenceType type) definitions :=
  .newCell (.inLeft wellFormed .unit)

theorem allocateInitialized_hasType
    {definitions : DataEnvironment} {context : Context}
    {type : Ty} {initializer : Expr}
    (typed : HasType context initializer type definitions) :
    HasType context (allocateInitialized type initializer) (referenceType type) definitions :=
  .newCell (.inRight .unit typed)

theorem read_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {reference : Expr} (reason : Word)
    (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context reference (referenceType type) definitions) :
    HasType context (read type reference reason) (LanguageResult.resultType type) definitions :=
  .caseE (.loadCell typed)
    (.inLeft wellFormed .word) (.inRight .word (.var rfl))

theorem write_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {reference value : Expr}
    (referenceTyped : HasType context reference (referenceType type) definitions)
    (valueTyped : HasType context value type definitions) :
    HasType context (write reference value) (LanguageResult.resultType .unit) definitions :=
  .inRight .word (.storeCell referenceTyped (.inRight .unit valueTyped))

theorem allocate_evaluates
    (type : Ty) (environment : Environment) (store : Store) :
    Evaluates environment store (allocate type)
      (.cellRef (cellType type) store.length) (store ++ [.inLeft type .unit]) :=
  .newCell (.inLeft .unit)

/-- Initializer effects happen before the location is allocated. -/
theorem allocateInitialized_evaluates
    {environment : Environment} {initialStore initializedStore : Store}
    {type : Ty} {initializer : Expr} {value : Value}
    (evaluated : Evaluates environment initialStore initializer value initializedStore) :
    Evaluates environment initialStore (allocateInitialized type initializer)
      (.cellRef (cellType type) initializedStore.length)
      (initializedStore ++ [.inRight .unit value]) :=
  .newCell (.inRight evaluated)

theorem read_failure
    {environment : Environment} {initialStore referenceStore : Store}
    {type : Ty} {reference : Expr} {location : Location} (reason : Word)
    (evaluated : Evaluates environment initialStore reference
      (.cellRef (cellType type) location) referenceStore)
    (uninitialized : referenceStore.read? location = some (.inLeft type .unit)) :
    Evaluates environment initialStore (read type reference reason)
      (.inLeft type (.word reason)) referenceStore :=
  .caseLeft (.loadCell evaluated uninitialized) (.inLeft .word)

theorem read_success
    {environment : Environment} {initialStore referenceStore : Store}
    {type : Ty} {reference : Expr} {location : Location} {value : Value}
    (reason : Word)
    (evaluated : Evaluates environment initialStore reference
      (.cellRef (cellType type) location) referenceStore)
    (initialized : referenceStore.read? location = some (.inRight .unit value)) :
    Evaluates environment initialStore (read type reference reason)
      (.inRight .word value) referenceStore :=
  .caseRight (.loadCell evaluated initialized) (.inRight (.var rfl))

/-- The value expression sees reference-expression effects, and the write uses
the store it produces. No values or locations are copied by this wrapper. -/
theorem write_evaluates
    {environment : Environment}
    {initialStore referenceStore valueStore finalStore : Store}
    {type : Ty} {reference value : Expr} {location : Location}
    {oldValue newValue : Value}
    (referenceEvaluated : Evaluates environment initialStore reference
      (.cellRef (cellType type) location) referenceStore)
    (readable : referenceStore.read? location = some oldValue)
    (valueEvaluated : Evaluates environment referenceStore value newValue valueStore)
    (written : valueStore.write? location (.inRight .unit newValue) = some finalStore) :
    Evaluates environment initialStore (write reference value)
      (.inRight .word .unit) finalStore :=
  .inRight (.storeCell referenceEvaluated readable (.inRight valueEvaluated) written)

end Solcore.Core.OptionalCell
end

section
-- leanmerge: from Solcore.Core.LocalSequence
/-! Local statement sequencing uses ordinary Core sums and cells. Continuations
are lowered in their lexical cell context before temporary result binders are
inserted. Evaluation laws use those actual inserted environments explicitly. -/

set_option autoImplicit false

namespace Solcore.Core.LocalSequence

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
end

section
-- leanmerge: from Solcore.Core.LocalControl
/-! Local control uses ordinary Core sums. A successful statement carries either
fallthrough (`left unit`) or an early return (`right value`); the outer language
result still carries failures. Branches and continuations start in their lexical
context. Evaluation laws expose every inserted binder and the shared store.
This envelope currently describes fallthrough and return, without loop-control
tags or an unrestricted termination claim. -/

set_option autoImplicit false

namespace Solcore.Core.LocalControl

theorem controlType_wellFormed
    {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) :
    Ty.WellFormed definitions (controlType type) :=
  .sum .unit wellFormed

theorem resultType_wellFormed
    {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) :
    Ty.WellFormed definitions (resultType type) :=
  LanguageResult.resultType_wellFormed (controlType_wellFormed wellFormed)

theorem fallthrough_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) :
    HasType context (fallthrough type) (resultType type) definitions :=
  LanguageResult.success_hasType (.inLeft wellFormed .unit)

theorem returned_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty} {value : Expr}
    (typed : HasType context value type definitions) :
    HasType context (returned value) (resultType type) definitions :=
  LanguageResult.success_hasType (.inRight .unit typed)

theorem returnValue_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty} {computation : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context computation (LanguageResult.resultType type) definitions) :
    HasType context (returnValue type computation) (resultType type) definitions :=
  LanguageResult.bind_hasType (controlType_wellFormed wellFormed) typed
    (returned_hasType (.var rfl))

theorem conditional_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {condition thenBranch elseBranch : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (thenTyped : HasType context thenBranch (resultType type) definitions)
    (elseTyped : HasType context elseBranch (resultType type) definitions) :
    HasType context (conditional type condition thenBranch elseBranch)
      (resultType type) definitions := by
  apply LanguageResult.bind_hasType (controlType_wellFormed wellFormed) conditionTyped
  apply HasType.ifE (.var rfl)
  · simpa [Context.insertAt, resultType] using thenTyped.weakenAt (inserted := .bool) 0
  · simpa [Context.insertAt, resultType] using elseTyped.weakenAt (inserted := .bool) 0

theorem choose_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {condition thenBranch elseBranch : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (thenTyped : HasType context thenBranch (LanguageResult.resultType type) definitions)
    (elseTyped : HasType context elseBranch (LanguageResult.resultType type) definitions) :
    HasType context (choose type condition thenBranch elseBranch)
      (LanguageResult.resultType type) definitions := by
  apply LanguageResult.bind_hasType wellFormed conditionTyped
  apply HasType.ifE (.var rfl)
  · simpa [Context.insertAt] using thenTyped.weakenAt (inserted := .bool) 0
  · simpa [Context.insertAt] using elseTyped.weakenAt (inserted := .bool) 0

theorem sequence_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {computation next : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (computationTyped : HasType context computation (resultType type) definitions)
    (nextTyped : HasType context next (resultType type) definitions) :
    HasType context (sequence type computation next) (resultType type) definitions := by
  apply LanguageResult.bind_hasType (controlType_wellFormed wellFormed) computationTyped
  apply HasType.caseE (.var rfl)
  · have controlNext := nextTyped.weakenAt (inserted := controlType type) 0
    have unitNext := controlNext.weakenAt (inserted := .unit) 0
    simpa [Context.insertAt, resultType] using unitNext
  · exact returned_hasType (.var rfl)

theorem finish_hasType
    {definitions : DataEnvironment} {context : Context} {type : Ty}
    {computation fallback : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (computationTyped : HasType context computation (resultType type) definitions)
    (fallbackTyped : HasType context fallback (LanguageResult.resultType type) definitions) :
    HasType context (finish type computation fallback)
      (LanguageResult.resultType type) definitions := by
  apply LanguageResult.bind_hasType wellFormed computationTyped
  apply HasType.caseE (.var rfl)
  · have controlFallback := fallbackTyped.weakenAt (inserted := controlType type) 0
    have unitFallback := controlFallback.weakenAt (inserted := .unit) 0
    simpa [Context.insertAt] using unitFallback
  · exact LanguageResult.success_hasType (.var rfl)

theorem fallthrough_evaluates (type : Ty) (environment : Environment) (store : Store) :
    Evaluates environment store (fallthrough type) (.inRight .word (.inLeft type .unit)) store :=
  .inRight (.inLeft .unit)

theorem returned_evaluates
    {environment : Environment} {initialStore finalStore : Store} {expression : Expr} {value : Value}
    (evaluation : Evaluates environment initialStore expression value finalStore) :
    Evaluates environment initialStore (returned expression)
      (.inRight .word (.inRight .unit value)) finalStore :=
  .inRight (.inRight evaluation)

theorem returnValue_failure
    {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft type (.word reason)) finalStore) :
    Evaluates environment initialStore (returnValue type computation)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem returnValue_success
    {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word value) finalStore) :
    Evaluates environment initialStore (returnValue type computation)
      (.inRight .word (.inRight .unit value)) finalStore :=
  LanguageResult.bind_success _ evaluation (returned_evaluates (.var rfl))

theorem conditional_failure
    {environment : Environment} {initialStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore condition
      (.inLeft .bool (.word reason)) finalStore) :
    Evaluates environment initialStore (conditional type condition thenBranch elseBranch)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem conditional_true
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value} (type : Ty)
    (conditionEvaluation : Evaluates environment initialStore condition
      (.inRight .word (.bool true)) branchStore)
    (branchEvaluation : Evaluates (.bool true :: environment) branchStore
      (thenBranch.weakenAt 0) result finalStore) :
    Evaluates environment initialStore (conditional type condition thenBranch elseBranch)
      result finalStore :=
  LanguageResult.bind_success _ conditionEvaluation (.ifTrue (.var rfl) branchEvaluation)

theorem conditional_false
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value} (type : Ty)
    (conditionEvaluation : Evaluates environment initialStore condition
      (.inRight .word (.bool false)) branchStore)
    (branchEvaluation : Evaluates (.bool false :: environment) branchStore
      (elseBranch.weakenAt 0) result finalStore) :
    Evaluates environment initialStore (conditional type condition thenBranch elseBranch)
      result finalStore :=
  LanguageResult.bind_success _ conditionEvaluation (.ifFalse (.var rfl) branchEvaluation)

theorem choose_failure
    {environment : Environment} {initialStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore condition
      (.inLeft .bool (.word reason)) finalStore) :
    Evaluates environment initialStore (choose type condition thenBranch elseBranch)
      (.inLeft type (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem choose_true
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value} (type : Ty)
    (conditionEvaluation : Evaluates environment initialStore condition
      (.inRight .word (.bool true)) branchStore)
    (branchEvaluation : Evaluates (.bool true :: environment) branchStore
      (thenBranch.weakenAt 0) result finalStore) :
    Evaluates environment initialStore (choose type condition thenBranch elseBranch)
      result finalStore :=
  LanguageResult.bind_success _ conditionEvaluation (.ifTrue (.var rfl) branchEvaluation)

theorem choose_false
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value} (type : Ty)
    (conditionEvaluation : Evaluates environment initialStore condition
      (.inRight .word (.bool false)) branchStore)
    (branchEvaluation : Evaluates (.bool false :: environment) branchStore
      (elseBranch.weakenAt 0) result finalStore) :
    Evaluates environment initialStore (choose type condition thenBranch elseBranch)
      result finalStore :=
  LanguageResult.bind_success _ conditionEvaluation (.ifFalse (.var rfl) branchEvaluation)

theorem sequence_failure
    {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft (controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (sequence type computation next)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem sequence_returned
    {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word (.inRight .unit value)) finalStore) :
    Evaluates environment initialStore (sequence type computation next)
      (.inRight .word (.inRight .unit value)) finalStore :=
  LanguageResult.bind_success _ evaluation
    (.caseRight (.var rfl) (returned_evaluates (.var rfl)))

theorem sequence_fallthrough
    {environment : Environment} {initialStore nextStore finalStore : Store}
    {computation next : Expr} {result : Value} (type : Ty)
    (computationEvaluation : Evaluates environment initialStore computation
      (.inRight .word (.inLeft type .unit)) nextStore)
    (nextEvaluation : Evaluates (.unit :: .inLeft type .unit :: environment) nextStore
      ((next.weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (sequence type computation next) result finalStore :=
  LanguageResult.bind_success _ computationEvaluation (.caseLeft (.var rfl) nextEvaluation)

theorem finish_failure
    {environment : Environment} {initialStore finalStore : Store}
    {computation fallback : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft (controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (finish type computation fallback)
      (.inLeft type (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem finish_returned
    {environment : Environment} {initialStore finalStore : Store}
    {computation fallback : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word (.inRight .unit value)) finalStore) :
    Evaluates environment initialStore (finish type computation fallback)
      (.inRight .word value) finalStore :=
  LanguageResult.bind_success _ evaluation (.caseRight (.var rfl) (.inRight (.var rfl)))

theorem finish_fallthrough
    {environment : Environment} {initialStore fallbackStore finalStore : Store}
    {computation fallback : Expr} {result : Value} (type : Ty)
    (computationEvaluation : Evaluates environment initialStore computation
      (.inRight .word (.inLeft type .unit)) fallbackStore)
    (fallbackEvaluation : Evaluates (.unit :: .inLeft type .unit :: environment) fallbackStore
      ((fallback.weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (finish type computation fallback) result finalStore :=
  LanguageResult.bind_success _ computationEvaluation (.caseLeft (.var rfl) fallbackEvaluation)

end Solcore.Core.LocalControl
end

section
-- leanmerge: from Solcore.Core.LocalAssignment
/-! Bare Word compound assignments use an optional payload snapshot captured
before the RHS. Absence is inspected after a successful RHS, so RHS failures
and effects retain their source order. All operations use ordinary Core. -/

set_option autoImplicit false

namespace Solcore.Core.LocalAssignment

theorem Operator.core_apply (operator : Operator) (left right : Word) :
    operator.core.apply (.word left) (.word right) = some (.word (operator.apply left right)) := by
  cases operator <;> rfl

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
end

section
-- leanmerge: from Solcore.Core.IntegerAssignment
/-! Bare Integer compound assignments use an optional payload snapshot captured
before the RHS. Absence is inspected after a successful RHS, so RHS failures
and effects retain their source order. All operations use ordinary Core. -/

set_option autoImplicit false

namespace Solcore.Core.IntegerAssignment

theorem Operator.core_apply (operator : Operator) (left right : Int) :
    operator.core.apply (.integer left) (.integer right) = some (.integer (operator.apply left right)) := by
  cases operator <;> rfl

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
end

section
-- leanmerge: from Solcore.Core.LocalLoop
/-! Ordinary Core loop control. Normal fallthrough/return occupies the left
side of a sum; break/continue occupies the right side. A loop installs a Unit
closure in its own optional cell, then calls it with a shared store. That
administrative cell is additional to source binding cells and remains in the
native Core store. Source heap correspondence must account for that location.
No new machine instruction or general termination theorem is introduced. -/

set_option autoImplicit false

namespace Solcore.Core.LocalLoop

theorem transferType_wellFormed (definitions : DataEnvironment) :
    Ty.WellFormed definitions transferType := .sum .unit .unit

theorem controlType_wellFormed {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : Ty.WellFormed definitions (controlType type) :=
  .sum (LocalControl.controlType_wellFormed wellFormed) (transferType_wellFormed definitions)

theorem resultType_wellFormed {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : Ty.WellFormed definitions (resultType type) :=
  LanguageResult.resultType_wellFormed (controlType_wellFormed wellFormed)

theorem functionType_wellFormed {definitions : DataEnvironment} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : Ty.WellFormed definitions (functionType type) :=
  .function .unit (resultType_wellFormed wellFormed)

theorem fallthrough_hasType {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : HasType context (fallthrough type) (resultType type) definitions :=
  LanguageResult.success_hasType (.inLeft (transferType_wellFormed definitions) (.inLeft wellFormed .unit))

theorem returned_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {value : Expr}
    (typed : HasType context value type definitions) : HasType context (returned value) (resultType type) definitions :=
  LanguageResult.success_hasType (.inLeft (transferType_wellFormed definitions) (.inRight .unit typed))

theorem breaking_hasType {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : HasType context (breaking type) (resultType type) definitions :=
  LanguageResult.success_hasType (.inRight (LocalControl.controlType_wellFormed wellFormed) (.inLeft .unit .unit))

theorem continuing_hasType {definitions : DataEnvironment} {context : Context} {type : Ty}
    (wellFormed : Ty.WellFormed definitions type) : HasType context (continuing type) (resultType type) definitions :=
  LanguageResult.success_hasType (.inRight (LocalControl.controlType_wellFormed wellFormed) (.inRight .unit .unit))

theorem returnValue_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {computation : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context computation (LanguageResult.resultType type) definitions) :
    HasType context (returnValue type computation) (resultType type) definitions :=
  LanguageResult.bind_hasType (controlType_wellFormed wellFormed) typed (returned_hasType (.var rfl))

theorem conditional_hasType {definitions : DataEnvironment} {context : Context} {type : Ty}
    {condition thenBranch elseBranch : Expr} (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (thenTyped : HasType context thenBranch (resultType type) definitions)
    (elseTyped : HasType context elseBranch (resultType type) definitions) :
    HasType context (conditional type condition thenBranch elseBranch) (resultType type) definitions :=
  LocalControl.choose_hasType (controlType_wellFormed wellFormed) conditionTyped thenTyped elseTyped

private theorem weakenThree {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (first second third : Ty) :
    HasType (third :: second :: first :: context) (((expression.weakenAt 0).weakenAt 0).weakenAt 0) type definitions := by
  have insertedFirst := typed.weakenAt (inserted := first) 0
  have insertedSecond := insertedFirst.weakenAt (inserted := second) 0
  simpa [Context.insertAt] using insertedSecond.weakenAt (inserted := third) 0

theorem sequence_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {computation next : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (computationTyped : HasType context computation (resultType type) definitions)
    (nextTyped : HasType context next (resultType type) definitions) :
    HasType context (sequence type computation next) (resultType type) definitions := by
  apply LanguageResult.bind_hasType (controlType_wellFormed wellFormed) computationTyped
  apply HasType.caseE (.var rfl)
  · apply HasType.caseE (.var rfl)
    · exact weakenThree nextTyped (controlType type) (LocalControl.controlType type) .unit
    · exact returned_hasType (.var rfl)
  · exact LanguageResult.success_hasType (.inRight (LocalControl.controlType_wellFormed wellFormed) (.var rfl))

theorem advance_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {computation next : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (computationTyped : HasType context computation (resultType type) definitions)
    (nextTyped : HasType context next (resultType type) definitions) :
    HasType context (advance type computation next) (resultType type) definitions := by
  apply LanguageResult.bind_hasType (controlType_wellFormed wellFormed) computationTyped
  apply HasType.caseE (.var rfl)
  · apply HasType.caseE (.var rfl)
    · exact weakenThree nextTyped (controlType type) (LocalControl.controlType type) .unit
    · exact returned_hasType (.var rfl)
  · apply HasType.caseE (.var rfl)
    · exact fallthrough_hasType wellFormed
    · exact weakenThree nextTyped (controlType type) transferType .unit

theorem liftControl_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {computation : Expr}
    (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context computation (LocalControl.resultType type) definitions) :
    HasType context (liftControl type computation) (resultType type) definitions :=
  LanguageResult.bind_hasType (controlType_wellFormed wellFormed) typed
    (LanguageResult.success_hasType (.inLeft (transferType_wellFormed definitions) (.var rfl)))

theorem toControl_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {computation : Expr}
    (reason : Word) (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context computation (resultType type) definitions) :
    HasType context (toControl type computation reason) (LocalControl.resultType type) definitions :=
  LanguageResult.bind_hasType (LocalControl.controlType_wellFormed wellFormed) typed
    (.caseE (.var rfl) (LanguageResult.success_hasType (.var rfl))
      (LanguageResult.failure_hasType (LocalControl.controlType_wellFormed wellFormed) .word))

theorem invoke_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {reference : Expr}
    (reason : Word) (wellFormed : Ty.WellFormed definitions type)
    (typed : HasType context reference (OptionalCell.referenceType (functionType type)) definitions) :
    HasType context (invoke type reference reason) (resultType type) definitions :=
  LanguageResult.bind_hasType (controlType_wellFormed wellFormed)
    (OptionalCell.read_hasType reason (functionType_wellFormed wellFormed) typed) (.apply (.var rfl) .unit)

private theorem weakenTwo {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (first second : Ty) :
    HasType (second :: first :: context) ((expression.weakenAt 0).weakenAt 0) type definitions := by
  have insertedFirst := typed.weakenAt (inserted := first) 0
  simpa [Context.insertAt] using insertedFirst.weakenAt (inserted := second) 0

theorem loopBody_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {condition body post : Expr}
    (reason : Word) (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (bodyTyped : HasType context body (resultType type) definitions)
    (postTyped : HasType context post (resultType type) definitions) :
    HasType (.unit :: OptionalCell.referenceType (functionType type) :: context)
      (loopBody type condition body post reason) (resultType type) definitions := by
  apply conditional_hasType wellFormed
  · exact weakenTwo conditionTyped _ _
  · apply advance_hasType wellFormed (weakenTwo bodyTyped _ _)
    exact advance_hasType wellFormed (weakenTwo postTyped _ _) (invoke_hasType reason wellFormed (.var rfl))
  · exact fallthrough_hasType wellFormed

theorem iterate_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {condition body post : Expr}
    (reason : Word) (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (bodyTyped : HasType context body (resultType type) definitions)
    (postTyped : HasType context post (resultType type) definitions) :
    HasType context (iterate type condition body post reason) (resultType type) definitions :=
  .letE (OptionalCell.allocate_hasType (functionType_wellFormed wellFormed))
    (.letE (.storeCell (.var rfl)
      (.inRight .unit (.lambda .unit (resultType_wellFormed wellFormed)
        (loopBody_hasType reason wellFormed conditionTyped bodyTyped postTyped))))
      (invoke_hasType reason wellFormed (.var rfl)))

theorem whileLoop_hasType {definitions : DataEnvironment} {context : Context} {type : Ty} {condition body : Expr}
    (reason : Word) (wellFormed : Ty.WellFormed definitions type)
    (conditionTyped : HasType context condition (LanguageResult.resultType .bool) definitions)
    (bodyTyped : HasType context body (resultType type) definitions) :
    HasType context (whileLoop type condition body reason) (resultType type) definitions :=
  iterate_hasType reason wellFormed conditionTyped bodyTyped (fallthrough_hasType wellFormed)

theorem fallthrough_evaluates (type : Ty) (environment : Environment) (store : Store) :
    Evaluates environment store (fallthrough type) (fallthroughValue type) store :=
  .inRight (.inLeft (.inLeft .unit))

theorem returned_evaluates {environment : Environment} {initialStore finalStore : Store}
    {expression : Expr} {value : Value} (evaluation : Evaluates environment initialStore expression value finalStore) :
    Evaluates environment initialStore (returned expression) (returnedValue value) finalStore :=
  .inRight (.inLeft (.inRight evaluation))

theorem breaking_evaluates (type : Ty) (environment : Environment) (store : Store) :
    Evaluates environment store (breaking type) (breakingValue type) store :=
  .inRight (.inRight (.inLeft .unit))

theorem continuing_evaluates (type : Ty) (environment : Environment) (store : Store) :
    Evaluates environment store (continuing type) (continuingValue type) store :=
  .inRight (.inRight (.inRight .unit))

theorem returnValue_failure {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (.inLeft type (.word reason)) finalStore) :
    Evaluates environment initialStore (returnValue type computation)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem returnValue_success {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (.inRight .word value) finalStore) :
    Evaluates environment initialStore (returnValue type computation) (returnedValue value) finalStore :=
  LanguageResult.bind_success _ evaluation (returned_evaluates (.var rfl))

theorem sequence_failure {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (.inLeft (controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (sequence type computation next)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem sequence_returned {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (returnedValue value) finalStore) :
    Evaluates environment initialStore (sequence type computation next) (returnedValue value) finalStore :=
  LanguageResult.bind_success _ evaluation
    (.caseLeft (.var rfl) (.caseRight (.var rfl) (returned_evaluates (.var rfl))))

theorem sequence_transfer {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {transfer : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word (.inRight (LocalControl.controlType type) transfer)) finalStore) :
    Evaluates environment initialStore (sequence type computation next)
      (.inRight .word (.inRight (LocalControl.controlType type) transfer)) finalStore :=
  LanguageResult.bind_success _ evaluation (.caseRight (.var rfl) (.inRight (.inRight (.var rfl))))

theorem sequence_fallthrough {environment : Environment} {initialStore nextStore finalStore : Store}
    {computation next : Expr} {result : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (fallthroughValue type) nextStore)
    (nextEvaluation : Evaluates
      (.unit :: .inLeft type .unit :: .inLeft transferType (.inLeft type .unit) :: environment)
      nextStore (((next.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (sequence type computation next) result finalStore :=
  LanguageResult.bind_success _ evaluation (.caseLeft (.var rfl) (.caseLeft (.var rfl) nextEvaluation))

theorem advance_failure {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (.inLeft (controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (advance type computation next)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem advance_returned {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (returnedValue value) finalStore) :
    Evaluates environment initialStore (advance type computation next) (returnedValue value) finalStore :=
  LanguageResult.bind_success _ evaluation
    (.caseLeft (.var rfl) (.caseRight (.var rfl) (returned_evaluates (.var rfl))))

theorem advance_breaking {environment : Environment} {initialStore finalStore : Store}
    {computation next : Expr} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (breakingValue type) finalStore) :
    Evaluates environment initialStore (advance type computation next) (fallthroughValue type) finalStore :=
  LanguageResult.bind_success _ evaluation
    (.caseRight (.var rfl) (.caseLeft (.var rfl) (fallthrough_evaluates _ _ _)))

theorem advance_fallthrough {environment : Environment} {initialStore nextStore finalStore : Store}
    {computation next : Expr} {result : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (fallthroughValue type) nextStore)
    (nextEvaluation : Evaluates
      (.unit :: .inLeft type .unit :: .inLeft transferType (.inLeft type .unit) :: environment)
      nextStore (((next.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (advance type computation next) result finalStore :=
  LanguageResult.bind_success _ evaluation (.caseLeft (.var rfl) (.caseLeft (.var rfl) nextEvaluation))

theorem advance_continuing {environment : Environment} {initialStore nextStore finalStore : Store}
    {computation next : Expr} {result : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (continuingValue type) nextStore)
    (nextEvaluation : Evaluates
      (.unit :: .inRight .unit .unit :: .inRight (LocalControl.controlType type) (.inRight .unit .unit) :: environment)
      nextStore (((next.weakenAt 0).weakenAt 0).weakenAt 0) result finalStore) :
    Evaluates environment initialStore (advance type computation next) result finalStore :=
  LanguageResult.bind_success _ evaluation (.caseRight (.var rfl) (.caseRight (.var rfl) nextEvaluation))

theorem liftControl_failure {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {reason : Word} (type : Ty)
    (evaluation : Evaluates environment initialStore computation
      (.inLeft (LocalControl.controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (liftControl type computation)
      (.inLeft (controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem liftControl_success {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {value : Value} (type : Ty)
    (evaluation : Evaluates environment initialStore computation (.inRight .word value) finalStore) :
    Evaluates environment initialStore (liftControl type computation)
      (.inRight .word (.inLeft transferType value)) finalStore :=
  LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl)))

theorem toControl_failure {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {reason : Word} (type : Ty) (escapedReason : Word)
    (evaluation : Evaluates environment initialStore computation (.inLeft (controlType type) (.word reason)) finalStore) :
    Evaluates environment initialStore (toControl type computation escapedReason)
      (.inLeft (LocalControl.controlType type) (.word reason)) finalStore :=
  LanguageResult.bind_failure _ evaluation

theorem toControl_normal {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {value : Value} (type : Ty) (escapedReason : Word)
    (evaluation : Evaluates environment initialStore computation (.inRight .word (.inLeft transferType value)) finalStore) :
    Evaluates environment initialStore (toControl type computation escapedReason) (.inRight .word value) finalStore :=
  LanguageResult.bind_success _ evaluation (.caseLeft (.var rfl) (.inRight (.var rfl)))

theorem toControl_transfer {environment : Environment} {initialStore finalStore : Store}
    {computation : Expr} {transfer : Value} (type : Ty) (escapedReason : Word)
    (evaluation : Evaluates environment initialStore computation
      (.inRight .word (.inRight (LocalControl.controlType type) transfer)) finalStore) :
    Evaluates environment initialStore (toControl type computation escapedReason)
      (.inLeft (LocalControl.controlType type) (.word escapedReason)) finalStore :=
  LanguageResult.bind_success _ evaluation (.caseRight (.var rfl) (.inLeft .word))

theorem invoke_failure {environment : Environment} {initialStore referenceStore : Store}
    {reference : Expr} {location : Location} (type : Ty) (reason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType (functionType type)) location) referenceStore)
    (absent : referenceStore.read? location = some (.inLeft (functionType type) .unit)) :
    Evaluates environment initialStore (invoke type reference reason)
      (.inLeft (controlType type) (.word reason)) referenceStore :=
  LanguageResult.bind_failure _ (OptionalCell.read_failure reason referenceEvaluation absent)

theorem invoke_success {environment captured : Environment} {initialStore referenceStore finalStore : Store}
    {reference closureBody : Expr} {location : Location} {result : Value} (type : Ty) (reason : Word)
    (referenceEvaluation : Evaluates environment initialStore reference
      (.cellRef (OptionalCell.cellType (functionType type)) location) referenceStore)
    (installed : referenceStore.read? location =
      some (.inRight .unit (.closure .unit (resultType type) closureBody captured)))
    (bodyEvaluation : Evaluates (.unit :: captured) referenceStore closureBody result finalStore) :
    Evaluates environment initialStore (invoke type reference reason) result finalStore :=
  LanguageResult.bind_success _ (OptionalCell.read_success reason referenceEvaluation installed)
    (.apply (.var rfl) .unit bodyEvaluation)

theorem iterate_evaluates {environment : Environment} {initialStore finalStore : Store}
    {condition body post : Expr} {result : Value} (type : Ty) (reason : Word)
    (entryEvaluation : Evaluates
      (.unit :: .cellRef (OptionalCell.cellType (functionType type)) initialStore.length :: environment)
      (initialStore ++ [.inRight .unit (installedClosure type condition body post reason initialStore.length environment)])
      (invoke type (.var 1) reason) result finalStore) :
    Evaluates environment initialStore (iterate type condition body post reason) result finalStore := by
  apply Evaluates.letE (OptionalCell.allocate_evaluates _ _ _)
  apply Evaluates.letE _ entryEvaluation
  apply Evaluates.storeCell (oldValue := .inLeft (functionType type) .unit) (.var rfl)
  · simp [Store.read?]
  · simpa only [installedClosure] using (Evaluates.inRight (Evaluates.lambda))
  · simp [Store.write?, installedClosure]

end Solcore.Core.LocalLoop
end

section
-- leanmerge: from Solcore.Core.LocalPrimitiveResults
/-! Primitive computations over ordinary language-result sums. Strict operands
run from left to right; a failure skips subsequent work. The Boolean helpers
evaluate their right operand only when the left value requires it. -/

set_option autoImplicit false

namespace Solcore.Core.LocalPrimitiveResults

theorem unary_hasType
    {definitions : DataEnvironment} {context : Context} {operator : UnaryOp} {operand : Expr}
    (typed : HasType context operand (LanguageResult.resultType operator.operandType) definitions) :
    HasType context (unary operator operand) (LanguageResult.resultType operator.resultType) definitions := by
  apply LanguageResult.bind_hasType (by cases operator <;> constructor) typed
  exact LanguageResult.success_hasType (.unary (.var rfl))

theorem binaryWith_hasType
    {definitions : DataEnvironment} {context : Context} {leftType rightType resultType : Ty}
    {left right body : Expr}
    (wellFormed : Ty.WellFormed definitions resultType)
    (leftTyped : HasType context left (LanguageResult.resultType leftType) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType rightType) definitions)
    (bodyTyped : HasType (rightType :: leftType :: context) body resultType definitions) :
    HasType context (binaryWith resultType left right body) (LanguageResult.resultType resultType) definitions := by
  apply LanguageResult.bind_hasType wellFormed leftTyped
  apply LanguageResult.bind_hasType wellFormed
  · simpa [Context.insertAt] using rightTyped.weakenAt (inserted := leftType) 0
  · exact LanguageResult.success_hasType bodyTyped

theorem binary_hasType
    {definitions : DataEnvironment} {context : Context} {operator : BinaryOp} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType operator.leftType) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType operator.rightType) definitions) :
    HasType context (binary operator left right) (LanguageResult.resultType operator.resultType) definitions :=
  binaryWith_hasType (by cases operator <;> constructor) leftTyped rightTyped (.binary (.var rfl) (.var rfl))

theorem logicalAnd_hasType
    {definitions : DataEnvironment} {context : Context} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType .bool) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType .bool) definitions) :
    HasType context (logicalAnd left right) (LanguageResult.resultType .bool) definitions :=
  LocalControl.choose_hasType .bool leftTyped rightTyped (LanguageResult.success_hasType .bool)

theorem logicalOr_hasType
    {definitions : DataEnvironment} {context : Context} {left right : Expr}
    (leftTyped : HasType context left (LanguageResult.resultType .bool) definitions)
    (rightTyped : HasType context right (LanguageResult.resultType .bool) definitions) :
    HasType context (logicalOr left right) (LanguageResult.resultType .bool) definitions :=
  LocalControl.choose_hasType .bool leftTyped (LanguageResult.success_hasType .bool) rightTyped

theorem unary_failure
    {environment : Environment} {before after : Store} {operator : UnaryOp} {operand : Expr} {reason : Word}
    (evaluation : Evaluates environment before operand (.inLeft operator.operandType (.word reason)) after) :
    Evaluates environment before (unary operator operand) (.inLeft operator.resultType (.word reason)) after :=
  LanguageResult.bind_failure _ evaluation

theorem unary_success
    {environment : Environment} {before after : Store} {operator : UnaryOp} {operand : Expr}
    {value result : Value}
    (evaluation : Evaluates environment before operand (.inRight .word value) after)
    (applied : operator.apply value = some result) :
    Evaluates environment before (unary operator operand) (.inRight .word result) after :=
  LanguageResult.bind_success _ evaluation (.inRight (.unary (.var rfl) applied))

theorem binaryWith_left_failure
    {environment : Environment} {before after : Store} {leftType resultType : Ty}
    {left right body : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft leftType (.word reason)) after) :
    Evaluates environment before (binaryWith resultType left right body)
      (.inLeft resultType (.word reason)) after :=
  LanguageResult.bind_failure _ evaluation

theorem binaryWith_right_failure
    {environment : Environment} {before middle after : Store} {rightType resultType : Ty}
    {left right body : Expr} {leftValue : Value} {reason : Word}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inLeft rightType (.word reason)) after) :
    Evaluates environment before (binaryWith resultType left right body)
      (.inLeft resultType (.word reason)) after :=
  LanguageResult.bind_success _ leftEvaluation (LanguageResult.bind_failure _ rightEvaluation)

theorem binaryWith_success
    {environment : Environment} {before middle operated after : Store} {resultType : Ty}
    {left right body : Expr} {leftValue rightValue result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word rightValue) operated)
    (bodyEvaluation : Evaluates (rightValue :: leftValue :: environment) operated body result after) :
    Evaluates environment before (binaryWith resultType left right body) (.inRight .word result) after :=
  LanguageResult.bind_success _ leftEvaluation
    (LanguageResult.bind_success _ rightEvaluation (.inRight bodyEvaluation))

theorem binary_left_failure
    {environment : Environment} {before after : Store} {operator : BinaryOp}
    {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft operator.leftType (.word reason)) after) :
    Evaluates environment before (binary operator left right) (.inLeft operator.resultType (.word reason)) after :=
  binaryWith_left_failure evaluation

theorem binary_right_failure
    {environment : Environment} {before middle after : Store} {operator : BinaryOp}
    {left right : Expr} {leftValue : Value} {reason : Word}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inLeft operator.rightType (.word reason)) after) :
    Evaluates environment before (binary operator left right) (.inLeft operator.resultType (.word reason)) after :=
  binaryWith_right_failure leftEvaluation rightEvaluation

theorem binary_success
    {environment : Environment} {before middle after : Store} {operator : BinaryOp}
    {left right : Expr} {leftValue rightValue result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word leftValue) middle)
    (rightEvaluation : Evaluates (leftValue :: environment) middle (right.weakenAt 0)
      (.inRight .word rightValue) after)
    (applied : operator.apply leftValue rightValue = some result) :
    Evaluates environment before (binary operator left right) (.inRight .word result) after :=
  binaryWith_success leftEvaluation rightEvaluation (.binary (.var rfl) (.var rfl) applied)

theorem logicalAnd_failure
    {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft .bool (.word reason)) after) :
    Evaluates environment before (logicalAnd left right) (.inLeft .bool (.word reason)) after :=
  LocalControl.choose_failure _ evaluation

theorem logicalOr_failure
    {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (evaluation : Evaluates environment before left (.inLeft .bool (.word reason)) after) :
    Evaluates environment before (logicalOr left right) (.inLeft .bool (.word reason)) after :=
  LocalControl.choose_failure _ evaluation

theorem logicalAnd_shortCircuit
    {environment : Environment} {before after : Store} {left right : Expr}
    (evaluation : Evaluates environment before left (.inRight .word (.bool false)) after) :
    Evaluates environment before (logicalAnd left right) (.inRight .word (.bool false)) after :=
  LocalControl.choose_false _ evaluation (by
    simp only [LanguageResult.success, Expr.weakenAt]
    exact .inRight .bool)

theorem logicalOr_shortCircuit
    {environment : Environment} {before after : Store} {left right : Expr}
    (evaluation : Evaluates environment before left (.inRight .word (.bool true)) after) :
    Evaluates environment before (logicalOr left right) (.inRight .word (.bool true)) after :=
  LocalControl.choose_true _ evaluation (by
    simp only [LanguageResult.success, Expr.weakenAt]
    exact .inRight .bool)

theorem logicalAnd_right
    {environment : Environment} {before middle after : Store} {left right : Expr} {result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word (.bool true)) middle)
    (rightEvaluation : Evaluates (.bool true :: environment) middle (right.weakenAt 0) result after) :
    Evaluates environment before (logicalAnd left right) result after :=
  LocalControl.choose_true _ leftEvaluation rightEvaluation

theorem logicalOr_right
    {environment : Environment} {before middle after : Store} {left right : Expr} {result : Value}
    (leftEvaluation : Evaluates environment before left (.inRight .word (.bool false)) middle)
    (rightEvaluation : Evaluates (.bool false :: environment) middle (right.weakenAt 0) result after) :
    Evaluates environment before (logicalOr left right) result after :=
  LocalControl.choose_false _ leftEvaluation rightEvaluation

end Solcore.Core.LocalPrimitiveResults
end

section
-- leanmerge: from Solcore.Core.TaggedFunction
/-! Ordinary Core functions with a source identity marker. Anonymous closures
carry `left unit` and compare unequal, including against themselves. Named
functions carry `right word`; the compiler must assign distinct words to
distinct declaration/evidence or builtin identities. This module neither
assigns those identities nor adds a primitive for closure equality. -/

set_option autoImplicit false

namespace Solcore.Core.TaggedFunction

theorem identityType_wellFormed {definitions : DataEnvironment} :
    Ty.WellFormed definitions identityType := .sum .unit .word

theorem functionType_wellFormed {definitions : DataEnvironment} {parameter result : Ty}
    (parameterWF : Ty.WellFormed definitions parameter)
    (resultWF : Ty.WellFormed definitions result) :
    Ty.WellFormed definitions (functionType parameter result) :=
  .product identityType_wellFormed
    (.function parameterWF (LanguageResult.resultType_wellFormed resultWF))

theorem anonymous_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr}
    (typed : HasType context function (.function parameter (LanguageResult.resultType result)) definitions) :
    HasType context (anonymous function) (functionType parameter result) definitions :=
  .pair (.inLeft .word .unit) typed

theorem identified_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr} (identity : Word)
    (typed : HasType context function (.function parameter (LanguageResult.resultType result)) definitions) :
    HasType context (identified identity function) (functionType parameter result) definitions :=
  .pair (.inRight .unit .word) typed

theorem call_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {callee arguments : Expr}
    (resultWF : Ty.WellFormed definitions result)
    (calleeTyped : HasType context callee (LanguageResult.resultType (functionType parameter result)) definitions)
    (argumentsTyped : HasType context arguments (LanguageResult.resultType parameter) definitions) :
    HasType context (call result callee arguments) (LanguageResult.resultType result) definitions := by
  apply LanguageResult.bind_hasType resultWF calleeTyped
  apply LanguageResult.bind_hasType resultWF
  · simpa [Context.insertAt] using argumentsTyped.weakenAt
      (inserted := functionType parameter result) 0
  · exact .apply (.second (.var rfl)) (.var rfl)

theorem equalBody_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} :
    HasType (functionType rightParameter rightResult ::
      functionType leftParameter leftResult :: context) equalBody .bool definitions :=
  .caseE (.first (.var rfl)) .bool
    (.caseE (.first (.var rfl)) .bool (.binary (.var rfl) (.var rfl)))

theorem equal_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} {left right : Expr}
    (leftTyped : HasType context left
      (LanguageResult.resultType (functionType leftParameter leftResult)) definitions)
    (rightTyped : HasType context right
      (LanguageResult.resultType (functionType rightParameter rightResult)) definitions) :
    HasType context (equal left right) (LanguageResult.resultType .bool) definitions :=
  LocalPrimitiveResults.binaryWith_hasType .bool leftTyped rightTyped equalBody_hasType

theorem call_callee_failure {environment : Environment} {before after : Store}
    {input result : Ty} {callee arguments : Expr} {reason : Word}
    (evaluation : Evaluates environment before callee (.inLeft input (.word reason)) after) :
    Evaluates environment before (call result callee arguments)
      (.inLeft result (.word reason)) after :=
  LanguageResult.bind_failure result evaluation

theorem call_argument_failure {environment : Environment} {before middle after : Store}
    {parameter result : Ty} {callee arguments : Expr} {function : Value} {reason : Word}
    (calleeEvaluation : Evaluates environment before callee (.inRight .word function) middle)
    (argumentsEvaluation : Evaluates (function :: environment) middle (arguments.weakenAt 0)
      (.inLeft parameter (.word reason)) after) :
    Evaluates environment before (call result callee arguments) (.inLeft result (.word reason)) after :=
  LanguageResult.bind_success result calleeEvaluation
    (LanguageResult.bind_failure result argumentsEvaluation)

theorem call_success {environment captured : Environment} {before middle applied after : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument value : Value}
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))) middle)
    (argumentsEvaluation : Evaluates
      (.pair identity (.closure parameter (LanguageResult.resultType result) body captured) :: environment)
      middle (arguments.weakenAt 0) (.inRight .word argument) applied)
    (bodyEvaluation : Evaluates (argument :: captured) applied body value after) :
    Evaluates environment before (call result callee arguments) value after :=
  LanguageResult.bind_success result calleeEvaluation
    (LanguageResult.bind_success result argumentsEvaluation
      (.apply (.second (.var rfl)) (.var rfl) bodyEvaluation))

/-- Identity comparison examines tags, never closure bodies or captures. -/
theorem equalBody_anonymous_left {environment : Environment} {store : Store}
    {left right : Value} {rightIdentity : Value} :
    Evaluates (.pair rightIdentity right :: .pair (.inLeft .word .unit) left :: environment)
      store equalBody (.bool false) store :=
  .caseLeft (.first (.var rfl)) .bool

theorem equalBody_anonymous_right {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity : Word} :
    Evaluates (.pair (.inLeft .word .unit) right :: .pair (.inRight .unit (.word leftIdentity)) left :: environment)
      store equalBody (.bool false) store :=
  .caseRight (.first (.var rfl)) (.caseLeft (.first (.var rfl)) .bool)

theorem equalBody_identified {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity rightIdentity : Word} :
    Evaluates (.pair (.inRight .unit (.word rightIdentity)) right ::
      .pair (.inRight .unit (.word leftIdentity)) left :: environment)
      store equalBody (.bool (leftIdentity == rightIdentity)) store :=
  .caseRight (.first (.var rfl))
    (.caseRight (.first (.var rfl)) (.binary (.var rfl) (.var rfl) rfl))

end Solcore.Core.TaggedFunction
end

section
-- leanmerge: from Solcore.Core.CallableContract
/-! Callable contracts are ordinary product payloads and static word dispatch.
The contract word is distinct from source function identity. Two guards preserve
callee → stage decision → arguments → arity decision → application order.
No syntax, checker, store, or machine rule is added. -/

set_option autoImplicit false

namespace Solcore.Core.CallableContract

theorem functionType_wellFormed {definitions : DataEnvironment} {parameter result : Ty}
    (parameterWF : Ty.WellFormed definitions parameter)
    (resultWF : Ty.WellFormed definitions result) :
    Ty.WellFormed definitions (functionType parameter result) :=
  .product (TaggedFunction.functionType_wellFormed parameterWF resultWF) .word

theorem wrap_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {function : Expr} (contract : Word)
    (typed : HasType context function (TaggedFunction.functionType parameter result) definitions) :
    HasType context (wrap contract function) (functionType parameter result) definitions :=
  .pair typed .word

theorem guardResult_hasType {definitions : DataEnvironment} {context : Context}
    (reason : Option Word) :
    HasType context (guardResult reason) (LanguageResult.resultType .unit) definitions := by
  cases reason with
  | none => exact .inRight .word .unit
  | some reason => exact .inLeft .unit .word

theorem dispatch_hasType {definitions : DataEnvironment} {context : Context}
    (gates : List Gate) (phase : Phase) (unknown : Word) {contract : Expr}
    (typed : HasType context contract .word definitions) :
    HasType context (dispatch gates phase unknown contract)
      (LanguageResult.resultType .unit) definitions := by
  induction gates with
  | nil => exact guardResult_hasType _
  | cons gate rest ih => exact .ifE (.binary typed .word) (guardResult_hasType _) ih

theorem call_hasType {definitions : DataEnvironment} {context : Context}
    {parameter result : Ty} {callee arguments : Expr} (gates : List Gate) (unknown : Word)
    (resultWF : Ty.WellFormed definitions result)
    (calleeTyped : HasType context callee (LanguageResult.resultType (functionType parameter result)) definitions)
    (argumentsTyped : HasType context arguments (LanguageResult.resultType parameter) definitions) :
    HasType context (call gates unknown result callee arguments)
      (LanguageResult.resultType result) definitions := by
  apply LanguageResult.bind_hasType resultWF calleeTyped
  apply LanguageResult.bind_hasType resultWF (dispatch_hasType _ _ _ (.second (.var rfl)))
  apply LanguageResult.bind_hasType resultWF
  · have once := argumentsTyped.weakenAt (inserted := functionType parameter result) 0
    have twice := once.weakenAt (inserted := Ty.unit) 0
    simpa [Context.insertAt] using twice
  apply LanguageResult.bind_hasType resultWF (dispatch_hasType _ _ _ (.second (.var rfl)))
  exact .apply (.second (.first (.var rfl))) (.var rfl)

theorem equalBody_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} :
    HasType (functionType rightParameter rightResult ::
      functionType leftParameter leftResult :: context) equalBody .bool definitions :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_hasType)

theorem equal_hasType {definitions : DataEnvironment} {context : Context}
    {leftParameter leftResult rightParameter rightResult : Ty} {left right : Expr}
    (leftTyped : HasType context left
      (LanguageResult.resultType (functionType leftParameter leftResult)) definitions)
    (rightTyped : HasType context right
      (LanguageResult.resultType (functionType rightParameter rightResult)) definitions) :
    HasType context (equal left right) (LanguageResult.resultType .bool) definitions :=
  LocalPrimitiveResults.binaryWith_hasType .bool leftTyped rightTyped equalBody_hasType

theorem equalBody_anonymous_left {environment : Environment} {store : Store}
    {left right rightIdentity : Value} {leftContract rightContract : Word} :
    Evaluates (.pair (.pair rightIdentity right) (.word rightContract) ::
      .pair (.pair (.inLeft .word .unit) left) (.word leftContract) :: environment)
      store equalBody (.bool false) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_anonymous_left)

theorem equalBody_anonymous_right {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity leftContract rightContract : Word} :
    Evaluates (.pair (.pair (.inLeft .word .unit) right) (.word rightContract) ::
      .pair (.pair (.inRight .unit (.word leftIdentity)) left) (.word leftContract) :: environment)
      store equalBody (.bool false) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_anonymous_right)

theorem equalBody_identified {environment : Environment} {store : Store}
    {left right : Value} {leftIdentity rightIdentity leftContract rightContract : Word} :
    Evaluates (.pair (.pair (.inRight .unit (.word rightIdentity)) right) (.word rightContract) ::
      .pair (.pair (.inRight .unit (.word leftIdentity)) left) (.word leftContract) :: environment)
      store equalBody (.bool (leftIdentity == rightIdentity)) store :=
  .letE (.first (.var rfl))
    (.letE (.first (.var rfl)) TaggedFunction.equalBody_identified)

theorem guardResult_evaluates {environment : Environment} {store : Store}
    (reason : Option Word) :
    Evaluates environment store (guardResult reason) (resultValue reason) store := by
  cases reason with
  | none => exact .inRight .unit
  | some reason => exact .inLeft .word

/-- The emitted decision has no store effects. The contract projection is a
pure value read; it can be reused by each branch without evaluating the callee. -/
theorem dispatch_evaluates {environment : Environment} {store : Store}
    (gates : List Gate) (phase : Phase) (unknown contractValue : Word) {contract : Expr}
    (read : Evaluates environment store contract (.word contractValue) store) :
    Evaluates environment store (dispatch gates phase unknown contract)
      (resultValue (decision gates phase unknown contractValue)) store := by
  induction gates with
  | nil => exact guardResult_evaluates _
  | cons gate rest ih =>
      cases sameId : (contractValue == gate.contract) with
      | false =>
          simp only [dispatch, decision, sameId, Bool.false_eq_true, ↓reduceIte]
          apply Evaluates.ifFalse
          · exact .binary read .word (by simp [BinaryOp.apply, sameId])
          · exact ih
      | true =>
          simp only [dispatch, decision, sameId, ↓reduceIte]
          apply Evaluates.ifTrue
          · exact .binary read .word (by simp [BinaryOp.apply, sameId])
          · exact guardResult_evaluates _

theorem dispatch_iff {environment : Environment} {store after : Store}
    (gates : List Gate) (phase : Phase) (unknown contractValue : Word) {contract : Expr} {value : Value}
    (read : Evaluates environment store contract (.word contractValue) store) :
    Evaluates environment store (dispatch gates phase unknown contract) value after ↔
      value = resultValue (decision gates phase unknown contractValue) ∧ after = store := by
  constructor
  · intro evaluation
    exact evaluation_deterministic evaluation (dispatch_evaluates gates phase unknown contractValue read)
  · rintro ⟨rfl, rfl⟩
    exact dispatch_evaluates gates phase unknown contractValue read

theorem wrap_evaluates {environment : Environment} {before after : Store}
    {function : Expr} {value : Value} (contract : Word)
    (evaluation : Evaluates environment before function value after) :
    Evaluates environment before (wrap contract function) (.pair value (.word contract)) after :=
  .pair evaluation .word

theorem call_callee_failure {environment : Environment} {before after : Store}
    {input result : Ty} {callee arguments : Expr} {reason : Word}
    (gates : List Gate) (unknown : Word)
    (evaluation : Evaluates environment before callee (.inLeft input (.word reason)) after) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after :=
  LanguageResult.bind_failure result evaluation

theorem call_stage_failure {environment : Environment} {before after : Store}
    {result : Ty} {callee arguments : Expr} {function : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (evaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) after)
    (rejected : decision gates .beforeArguments unknown contract = some reason) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result evaluation
  apply LanguageResult.bind_failure result
  have gate := dispatch_evaluates gates .beforeArguments unknown contract
    (Evaluates.second (Evaluates.var rfl) : Evaluates
      (.pair function (.word contract) :: environment) after (.second (.var 0)) (.word contract) after)
  simpa [rejected, resultValue] using gate

theorem call_argument_failure {environment : Environment} {before middle after : Store}
    {parameter result : Ty} {callee arguments : Expr} {function : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) middle)
    (accepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit :: .pair function (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inLeft parameter (.word reason)) after) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair function (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [accepted, resultValue] using gate
  exact LanguageResult.bind_failure result argumentsEvaluation

theorem call_arity_failure {environment : Environment} {before middle after : Store}
    {result : Ty} {callee arguments : Expr} {function argument : Value} {contract reason : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair function (.word contract))) middle)
    (accepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit :: .pair function (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) after)
    (rejected : decision gates .beforeApplication unknown contract = some reason) :
    Evaluates environment before (call gates unknown result callee arguments)
      (.inLeft result (.word reason)) after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair function (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [accepted, resultValue] using gate
  apply LanguageResult.bind_success result argumentsEvaluation
  apply LanguageResult.bind_failure result
  have gate := dispatch_evaluates gates .beforeApplication unknown contract
    (Evaluates.second (Evaluates.var rfl) : Evaluates
      (argument :: .unit :: .pair function (.word contract) :: environment) after
      (.second (.var 2)) (.word contract) after)
  simpa [rejected, resultValue] using gate

theorem call_success {environment captured : Environment} {before middle applied after : Store}
    {parameter result : Ty} {callee arguments body : Expr} {identity argument value : Value} {contract : Word}
    (gates : List Gate) (unknown : Word)
    (calleeEvaluation : Evaluates environment before callee
      (.inRight .word (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
        (.word contract))) middle)
    (stageAccepted : decision gates .beforeArguments unknown contract = none)
    (argumentsEvaluation : Evaluates (.unit ::
      .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured)) (.word contract) :: environment)
      middle ((arguments.weakenAt 0).weakenAt 0) (.inRight .word argument) applied)
    (arityAccepted : decision gates .beforeApplication unknown contract = none)
    (bodyEvaluation : Evaluates (argument :: captured) applied body value after) :
    Evaluates environment before (call gates unknown result callee arguments) value after := by
  apply LanguageResult.bind_success result calleeEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeArguments unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (.pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
          (.word contract) :: environment) middle (.second (.var 0)) (.word contract) middle)
    simpa [stageAccepted, resultValue] using gate
  apply LanguageResult.bind_success result argumentsEvaluation
  apply LanguageResult.bind_success result
  · have gate := dispatch_evaluates gates .beforeApplication unknown contract
      (Evaluates.second (Evaluates.var rfl) : Evaluates
        (argument :: .unit ::
          .pair (.pair identity (.closure parameter (LanguageResult.resultType result) body captured))
            (.word contract) :: environment) applied (.second (.var 2)) (.word contract) applied)
    simpa [arityAccepted, resultValue] using gate
  exact .apply (.second (.first (.var rfl))) (.var rfl) bodyEvaluation

end Solcore.Core.CallableContract
end
