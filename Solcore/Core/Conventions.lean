import Solcore.Core.LanguageResult

/-!
# Conventions of compiled code

How the compiler encodes source constructs in ordinary Core. None of this adds syntax or a machine
rule. These are the definitions; their laws are in `Internal/ConventionLaws`.

- `OptionalCell`: a mutable binding, a cell holding an optional value.
- `LocalSequence`: declarations, assignment and sequencing.
- `LocalControl`: fallthrough and early return.
- `LocalLoop`: `LocalLoop.whileLoop` with break and continue.
- `LocalAssignment`, `IntegerAssignment`: compound assignment to Word and Integer bindings.
- `LocalPrimitiveResults`: primitives over language results.
- `TaggedFunction`: functions with a source identity.
- `CallableContract`: callable contract values and their dispatch.
-/

section
-- leanmerge: from Solcore.Core.Internal.OptionalCellDefs
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

end Solcore.Core.OptionalCell
end

section
-- leanmerge: from Solcore.Core.Internal.LocalSequenceDefs
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

end Solcore.Core.LocalSequence
end

section
-- leanmerge: from Solcore.Core.Internal.LocalControlDefs
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

end Solcore.Core.LocalControl
end

section
-- leanmerge: from Solcore.Core.Internal.LocalAssignmentDefs
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

end Solcore.Core.LocalAssignment
end

section
-- leanmerge: from Solcore.Core.Internal.IntegerAssignmentDefs
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

end Solcore.Core.IntegerAssignment
end

section
-- leanmerge: from Solcore.Core.Internal.LocalLoopDefs
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

def fallthroughValue (type : Ty) : Value := .inRight .word (.inLeft transferType (.inLeft type .unit))

def returnedValue (value : Value) : Value := .inRight .word (.inLeft transferType (.inRight .unit value))

def breakingValue (type : Ty) : Value := .inRight .word (.inRight (LocalControl.controlType type) (.inLeft .unit .unit))

def continuingValue (type : Ty) : Value := .inRight .word (.inRight (LocalControl.controlType type) (.inRight .unit .unit))

/-- The closure contains a reference to the optional cell that stores it.
The finite value represents the cycle through its location, without unfolding
the heap recursively or replacing a missing function with a dummy. -/
def installedClosure (type : Ty) (condition body post : Expr) (reason : Word)
    (location : Location) (environment : Environment) : Value :=
  .closure .unit (resultType type) (loopBody type condition body post reason)
    (.cellRef (OptionalCell.cellType (functionType type)) location :: environment)

end Solcore.Core.LocalLoop
end

section
-- leanmerge: from Solcore.Core.Internal.LocalPrimitiveResultsDefs
/-! Primitive computations over ordinary language-result sums. Strict operands
run from left to right; a failure skips subsequent work. The Boolean helpers
evaluate their right operand only when the left value requires it. -/

set_option autoImplicit false

namespace Solcore.Core.LocalPrimitiveResults

def unary (operator : UnaryOp) (operand : Expr) : Expr :=
  LanguageResult.bind operator.resultType operand
    (LanguageResult.success (.unary operator (.var 0)))

/-- `body` returns a raw value under right payload, left payload, outer scope.
This also supports comparisons built from existing Core primitives. -/
def binaryWith (resultType : Ty) (left right body : Expr) : Expr :=
  LanguageResult.bind resultType left
    (LanguageResult.bind resultType (right.weakenAt 0) (LanguageResult.success body))

def binary (operator : BinaryOp) (left right : Expr) : Expr :=
  binaryWith operator.resultType left right (.binary operator (.var 1) (.var 0))

def logicalAnd (left right : Expr) : Expr :=
  LocalControl.choose .bool left right (LanguageResult.success (.bool false))

def logicalOr (left right : Expr) : Expr :=
  LocalControl.choose .bool left (LanguageResult.success (.bool true)) right

end Solcore.Core.LocalPrimitiveResults
end

section
-- leanmerge: from Solcore.Core.Internal.TaggedFunctionDefs
/-! Ordinary Core functions with a source identity marker. Anonymous closures
carry `left unit` and compare unequal, including against themselves. Named
functions carry `right word`; the compiler must assign distinct words to
distinct declaration/evidence or builtin identities. This module neither
assigns those identities nor adds a primitive for closure equality. -/

set_option autoImplicit false

namespace Solcore.Core.TaggedFunction

def identityType : Ty := .sum .unit .word

def functionType (parameter result : Ty) : Ty :=
  .product identityType (.function parameter (LanguageResult.resultType result))

def anonymous (function : Expr) : Expr :=
  .pair (.inLeft .word .unit) function

def identified (identity : Word) (function : Expr) : Expr :=
  .pair (.inRight .unit (.word identity)) function

/-- The indirect callee runs before its argument bundle. The closure receives
the bundle and the latest shared store; a failure skips the remaining work. -/
def call (result : Ty) (callee arguments : Expr) : Expr :=
  LanguageResult.bind result callee
    (LanguageResult.bind result (arguments.weakenAt 0)
      (.apply (.second (.var 1)) (.var 0)))

/-- A raw comparison under right function, left function, outer context. -/
def equalBody : Expr :=
  .caseE (.first (.var 1)) (.bool false)
    (.caseE (.first (.var 1)) (.bool false)
      (.binary .wordEq (.var 1) (.var 0)))

def equal (left right : Expr) : Expr :=
  LocalPrimitiveResults.binaryWith .bool left right equalBody

end Solcore.Core.TaggedFunction
end

section
-- leanmerge: from Solcore.Core.Internal.CallableContractDefs
/-! Callable contracts are ordinary product payloads and static word dispatch.
The contract word is distinct from source function identity. Two guards preserve
callee → stage decision → arguments → arity decision → application order.
No syntax, checker, store, or machine rule is added. -/

set_option autoImplicit false

namespace Solcore.Core.CallableContract

def functionType (parameter result : Ty) : Ty :=
  .product (TaggedFunction.functionType parameter result) .word

def wrap (contract : Word) (function : Expr) : Expr :=
  .pair function (.word contract)

inductive Phase where
  | beforeArguments
  | beforeApplication
  deriving Repr, BEq, DecidableEq

structure Gate where
  contract : Word
  beforeArguments : Option Word
  beforeApplication : Option Word
  deriving Repr, BEq, DecidableEq

def Gate.reason (gate : Gate) : Phase → Option Word
  | .beforeArguments => gate.beforeArguments
  | .beforeApplication => gate.beforeApplication

def decision (gates : List Gate) (phase : Phase) (unknown contract : Word) : Option Word :=
  match gates with
  | [] => some unknown
  | gate :: rest => if contract == gate.contract then gate.reason phase
      else decision rest phase unknown contract

def guardResult : Option Word → Expr
  | none => LanguageResult.success .unit
  | some reason => LanguageResult.failure .unit (.word reason)

def dispatch (gates : List Gate) (phase : Phase) (unknown : Word) (contract : Expr) : Expr :=
  match gates with
  | [] => guardResult (some unknown)
  | gate :: rest => .ifE (.binary .wordEq contract (.word gate.contract))
      (guardResult (gate.reason phase)) (dispatch rest phase unknown contract)

def call (gates : List Gate) (unknown : Word) (result : Ty) (callee arguments : Expr) : Expr :=
  LanguageResult.bind result callee
    (LanguageResult.bind result
      (dispatch gates .beforeArguments unknown (.second (.var 0)))
      (LanguageResult.bind result ((arguments.weakenAt 0).weakenAt 0)
        (LanguageResult.bind result
          (dispatch gates .beforeApplication unknown (.second (.var 2)))
          (.apply (.second (.first (.var 3))) (.var 1)))))

/-- Equality sees the existing identity tag inside the wrapper. Contract words
can differ without changing named identity; anonymous functions stay unequal. -/
def equalBody : Expr :=
  .letE (.first (.var 1)) (.letE (.first (.var 1)) TaggedFunction.equalBody)

def equal (left right : Expr) : Expr :=
  LocalPrimitiveResults.binaryWith .bool left right equalBody

def resultValue : Option Word → Value
  | none => .inRight .word .unit
  | some reason => .inLeft .unit (.word reason)

end Solcore.Core.CallableContract
end
