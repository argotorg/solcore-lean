import Solcore.Core.LanguageResult
import Solcore.Core.Eval

/-! Mutable source bindings use ordinary Core cells with an explicit optional
payload. An absent value becomes a language failure on read. References and
closures keep the same shared store as ordinary Core values. -/

set_option autoImplicit false

namespace Solcore.Core.OptionalCell

/-- The left payload marks an uninitialized binding; the right contains its value. -/
def cellType (type : Ty) : Ty := .sum .unit type

def referenceType (type : Ty) : Ty := .cell (cellType type)

/-- Allocate without constructing a value of the binding's declared type. -/
def allocate (type : Ty) : Expr :=
  .newCell (cellType type) (.inLeft type .unit)

def allocateInitialized (type : Ty) (initializer : Expr) : Expr :=
  .newCell (cellType type) (.inRight .unit initializer)

/-- The caller supplies the reason code for an uninitialized read. Both branches
are ordinary Core expressions and finish with a language result. -/
def read (type : Ty) (reference : Expr) (uninitializedReason : Word) : Expr :=
  .caseE (.loadCell reference)
    (LanguageResult.failure type (.word uninitializedReason))
    (LanguageResult.success (.var 0))

/-- Write an initialized payload and return successful Unit. -/
def write (reference value : Expr) : Expr :=
  LanguageResult.success (.storeCell reference (.inRight .unit value))

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
