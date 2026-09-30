import Solcore.Core.LocalSequence

/-! Local control uses ordinary Core sums. A successful statement carries either
fallthrough (`left unit`) or an early return (`right value`); the outer language
result still carries failures. Branches and continuations start in their lexical
context. Evaluation laws expose every inserted binder and the shared store.
This envelope currently describes fallthrough and return, without loop-control
tags or an unrestricted termination claim. -/

set_option autoImplicit false

namespace Solcore.Core.LocalControl

def controlType (type : Ty) : Ty := .sum .unit type

def resultType (type : Ty) : Ty := LanguageResult.resultType (controlType type)

def fallthrough (type : Ty) : Expr :=
  LanguageResult.success (.inLeft type .unit)

def returned (value : Expr) : Expr :=
  LanguageResult.success (.inRight .unit value)

def returnValue (type : Ty) (computation : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation (returned (.var 0))

/-- A conditional expression whose branches produce ordinary language results. -/
def choose (type : Ty) (condition thenBranch elseBranch : Expr) : Expr :=
  LanguageResult.bind type condition
    (.ifE (.var 0) (thenBranch.weakenAt 0) (elseBranch.weakenAt 0))

def conditional (type : Ty) (condition thenBranch elseBranch : Expr) : Expr :=
  LanguageResult.bind (controlType type) condition
    (.ifE (.var 0) (thenBranch.weakenAt 0) (elseBranch.weakenAt 0))

/-- Only fallthrough runs `next`. A block's internal lexical bindings have
already been discharged by its result, while its heap effects remain shared. -/
def sequence (type : Ty) (computation next : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation
    (.caseE (.var 0) ((next.weakenAt 0).weakenAt 0) (returned (.var 0)))

/-- Remove the statement envelope at a function boundary. `fallback` handles
fallthrough in the outer lexical context, for example successful Unit or a
language failure for a missing return. -/
def finish (type : Ty) (computation fallback : Expr) : Expr :=
  LanguageResult.bind type computation
    (.caseE (.var 0) ((fallback.weakenAt 0).weakenAt 0)
      (LanguageResult.success (.var 0)))

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
