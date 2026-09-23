import Solcore.TypeSystem.Type

/-!
Static summaries for source-statement control transfer.

The semantic summary is kept separate from the legacy type annotation retained
on statement nodes.  This matters for paths containing break/continue and for
the source convention that a final semicolon-free expression can provide a
function result.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

/-- Control assumptions at one statement occurrence. -/
structure ControlContext where
  returnType : TypeSystem.Ty
  loopDepth : Nat := 0
  deriving Repr, DecidableEq

namespace ControlContext

def enterLoop (control : ControlContext) : ControlContext :=
  { control with loopDepth := control.loopDepth + 1 }

def resetLoop (control : ControlContext) : ControlContext :=
  { control with loopDepth := 0 }

def loopAllowed (control : ControlContext) : Prop :=
  0 < control.loopDepth

end ControlContext

/-- Possible transfers of a well-typed statement fragment.  `fallthrough`
records the value type produced only when ordinary control reaches the end. -/
structure ControlSummary where
  fallthrough : Option TypeSystem.Ty
  mayReturn : Bool := false
  mayBreak : Bool := false
  mayContinue : Bool := false
  deriving Repr, DecidableEq

namespace ControlSummary

def ordinary (type : TypeSystem.Ty) : ControlSummary :=
  { fallthrough := some type }

def returned : ControlSummary :=
  { fallthrough := none, mayReturn := true }

def breaking : ControlSummary :=
  { fallthrough := none, mayBreak := true }

def continuing : ControlSummary :=
  { fallthrough := none, mayContinue := true }

def canFallthrough (summary : ControlSummary) : Bool :=
  summary.fallthrough.isSome

/-- Sequential composition; tail transfers are reachable only along an
ordinary fallthrough path from the head. -/
def sequence (head tail : ControlSummary) : ControlSummary := {
  fallthrough := if head.canFallthrough then tail.fallthrough else none
  mayReturn := head.mayReturn || (head.canFallthrough && tail.mayReturn)
  mayBreak := head.mayBreak || (head.canFallthrough && tail.mayBreak)
  mayContinue := head.mayContinue ||
    (head.canFallthrough && tail.mayContinue)
}

/-- Merge two conditionally selected branches.  A branch-local value is
erased because `if` and `match` are statements rather than expressions. -/
def branches (left right : ControlSummary) : ControlSummary := {
  fallthrough :=
    if left.canFallthrough || right.canFallthrough then some .unit else none
  mayReturn := left.mayReturn || right.mayReturn
  mayBreak := left.mayBreak || right.mayBreak
  mayContinue := left.mayContinue || right.mayContinue
}

/-- A scoped statement erases an ordinary inner value while preserving
nonlocal control transfer. -/
def eraseValue (inner : ControlSummary) : ControlSummary := {
  inner with fallthrough := inner.fallthrough.map fun _ => .unit
}

/-- A loop always has the condition-false fallthrough path.  Break and
continue are consumed; returns propagate. -/
def loop (body : ControlSummary) : ControlSummary := {
  fallthrough := some .unit
  mayReturn := body.mayReturn
}

@[simp] theorem canFallthrough_ordinary (type : TypeSystem.Ty) :
    (ordinary type).canFallthrough = true := rfl

@[simp] theorem canFallthrough_returned : returned.canFallthrough = false := rfl

@[simp] theorem sequence_ordinary (type : TypeSystem.Ty)
    (tail : ControlSummary) :
    sequence (ordinary type) tail = tail := by
  cases tail
  rfl

end ControlSummary

/-- Static result attached to one statement derivation. -/
structure StatementFacts where
  type : TypeSystem.Ty
  hasValue : Bool
  sawReturn : Bool
  control : ControlSummary
  deriving Repr, DecidableEq

/-- Static result of a statement sequence. -/
structure BodyFacts where
  type : TypeSystem.Ty
  sawReturn : Bool
  control : ControlSummary
  deriving Repr, DecidableEq

namespace BodyFacts

def empty : BodyFacts := {
  type := .unit
  sawReturn := false
  control := .ordinary .unit
}

def singleton (statement : StatementFacts) : BodyFacts := {
  type := if statement.sawReturn || statement.hasValue then
    statement.type else .unit
  sawReturn := statement.sawReturn
  control := statement.control
}

def cons (head : StatementFacts) (tail : BodyFacts) : BodyFacts := {
  type := if tail.sawReturn then tail.type
    else if head.sawReturn then head.type else tail.type
  sawReturn := head.sawReturn || tail.sawReturn
  control := head.control.sequence tail.control
}

end BodyFacts

/-- A closed body cannot let loop-local transfer escape and either returns or
falls through with the declaration's result type. -/
def BodyCompletes (expected : TypeSystem.Ty) (facts : BodyFacts) : Prop :=
  facts.control.mayBreak = false ∧
    facts.control.mayContinue = false ∧
    ((facts.control.fallthrough = none ∧ facts.control.mayReturn = true) ∨
      facts.control.fallthrough = some expected)

end Solcore.SourceSemantics
