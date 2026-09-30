import Solcore.Core.LocalControl

/-! Ordinary Core loop control. Normal fallthrough/return occupies the left
side of a sum; break/continue occupies the right side. A loop installs a Unit
closure in its own optional cell, then calls it with a shared store. That
administrative cell is additional to source binding cells and remains in the
native Core store. Source heap correspondence must account for that location.
No new machine instruction or general termination theorem is introduced. -/

set_option autoImplicit false

namespace Solcore.Core.LocalLoop

def transferType : Ty := .sum .unit .unit
def controlType (type : Ty) : Ty := .sum (LocalControl.controlType type) transferType
def resultType (type : Ty) : Ty := LanguageResult.resultType (controlType type)
def functionType (type : Ty) : Ty := .function .unit (resultType type)

def fallthrough (type : Ty) : Expr :=
  LanguageResult.success (.inLeft transferType (.inLeft type .unit))

def returned (value : Expr) : Expr :=
  LanguageResult.success (.inLeft transferType (.inRight .unit value))

def breaking (type : Ty) : Expr :=
  LanguageResult.success (.inRight (LocalControl.controlType type) (.inLeft .unit .unit))

def continuing (type : Ty) : Expr :=
  LanguageResult.success (.inRight (LocalControl.controlType type) (.inRight .unit .unit))

def returnValue (type : Ty) (computation : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation (returned (.var 0))

def conditional (type : Ty) (condition thenBranch elseBranch : Expr) : Expr :=
  LocalControl.choose (controlType type) condition thenBranch elseBranch

/-- Ordinary sequencing stops at return, break, continue or failure. -/
def sequence (type : Ty) (computation next : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation
    (.caseE (.var 0)
      (.caseE (.var 0) (((next.weakenAt 0).weakenAt 0).weakenAt 0) (returned (.var 0)))
      (LanguageResult.success (.inRight (LocalControl.controlType type) (.var 0))))

/-- At a loop boundary, break becomes fallthrough. Fallthrough and continue
both run `next`; return and failure still stop. This also specifies total
behavior for post computations, though source for-header items cannot transfer
control in the current language. -/
def advance (type : Ty) (computation next : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation
    (.caseE (.var 0)
      (.caseE (.var 0) (((next.weakenAt 0).weakenAt 0).weakenAt 0) (returned (.var 0)))
      (.caseE (.var 0) (fallthrough type) (((next.weakenAt 0).weakenAt 0).weakenAt 0)))

def liftControl (type : Ty) (computation : Expr) : Expr :=
  LanguageResult.bind (controlType type) computation
    (LanguageResult.success (.inLeft transferType (.var 0)))

/-- Consume the extended envelope at a surrounding non-loop boundary. Escaped
break/continue becomes the caller's language failure, preserving its effects. -/
def toControl (type : Ty) (computation : Expr) (escapedReason : Word) : Expr :=
  LanguageResult.bind (LocalControl.controlType type) computation
    (.caseE (.var 0) (LanguageResult.success (.var 0))
      (LanguageResult.failure (LocalControl.controlType type) (.word escapedReason)))

def invoke (type : Ty) (reference : Expr) (uninitializedReason : Word) : Expr :=
  LanguageResult.bind (controlType type)
    (OptionalCell.read (functionType type) reference uninitializedReason)
    (.apply (.var 0) .unit)

/-- Closure entry receives Unit, its self reference, then the lexical context.
The self call is in tail position, after post effects have completed. -/
def loopBody (type : Ty) (condition body post : Expr) (uninitializedReason : Word) : Expr :=
  conditional type ((condition.weakenAt 0).weakenAt 0)
    (advance type ((body.weakenAt 0).weakenAt 0)
      (advance type ((post.weakenAt 0).weakenAt 0)
        (invoke type (.var 1) uninitializedReason)))
    (fallthrough type)

/-- Install the self closure before its first invocation. Body fallthrough or
continue executes post, then rechecks the condition; break skips post. -/
def iterate (type : Ty) (condition body post : Expr) (uninitializedReason : Word) : Expr :=
  .letE (OptionalCell.allocate (functionType type))
    (.letE (.storeCell (.var 0)
      (.inRight .unit (.lambda .unit (resultType type)
        (loopBody type condition body post uninitializedReason))))
      (invoke type (.var 1) uninitializedReason))

def whileLoop (type : Ty) (condition body : Expr) (uninitializedReason : Word) : Expr :=
  iterate type condition body (fallthrough type) uninitializedReason

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

def fallthroughValue (type : Ty) : Value := .inRight .word (.inLeft transferType (.inLeft type .unit))
def returnedValue (value : Value) : Value := .inRight .word (.inLeft transferType (.inRight .unit value))
def breakingValue (type : Ty) : Value := .inRight .word (.inRight (LocalControl.controlType type) (.inLeft .unit .unit))
def continuingValue (type : Ty) : Value := .inRight .word (.inRight (LocalControl.controlType type) (.inRight .unit .unit))

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

/-- The closure contains a reference to the optional cell that stores it.
The finite value represents the cycle through its location, without unfolding
the heap recursively or replacing a missing function with a dummy. -/
def installedClosure (type : Ty) (condition body post : Expr) (reason : Word)
    (location : Location) (environment : Environment) : Value :=
  .closure .unit (resultType type) (loopBody type condition body post reason)
    (.cellRef (OptionalCell.cellType (functionType type)) location :: environment)

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
