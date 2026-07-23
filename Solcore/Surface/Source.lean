set_option autoImplicit false

namespace Solcore.Surface

/--
A source file before workspace validation. Paths are carried explicitly so that
every diagnostic span identifies its owner.
-/
structure SourceFile where
  path : String
  content : String
  deriving Repr, BEq, DecidableEq

/-- A half-open UTF-8 byte range in one source file. -/
structure SourceSpan where
  source : String
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

namespace SourceSpan

def length (span : SourceSpan) : Nat :=
  span.endByte - span.startByte

/-- Declarative ownership, ordering, and bounds requirements for a span. -/
def ValidFor (span : SourceSpan) (file : SourceFile) : Prop :=
  (span.source = file.path ∧
    span.startByte ≤ span.endByte) ∧
    span.endByte ≤ file.content.utf8ByteSize

/-- Executable decision procedure for `ValidFor`. -/
def isValidFor (span : SourceSpan) (file : SourceFile) : Bool :=
  span.source == file.path &&
    span.startByte ≤ span.endByte &&
    span.endByte ≤ file.content.utf8ByteSize

theorem isValidFor_eq_true_iff (span : SourceSpan) (file : SourceFile) :
    span.isValidFor file = true ↔ span.ValidFor file := by
  simp [isValidFor, ValidFor]

/-- Declarative containment of one half-open span by another. -/
def Contains (outer inner : SourceSpan) : Prop :=
  (outer.source = inner.source ∧
    outer.startByte ≤ inner.startByte) ∧
    (inner.startByte ≤ inner.endByte ∧
      inner.endByte ≤ outer.endByte)

/-- Executable decision procedure for `Contains`. -/
def contains (outer inner : SourceSpan) : Bool :=
  outer.source == inner.source &&
    outer.startByte ≤ inner.startByte &&
    inner.startByte ≤ inner.endByte &&
    inner.endByte ≤ outer.endByte

theorem contains_eq_true_iff (outer inner : SourceSpan) :
    outer.contains inner = true ↔ outer.Contains inner := by
  simp [contains, Contains, and_assoc]

def cover (first last : SourceSpan) : SourceSpan := {
  source := first.source
  startByte := first.startByte
  endByte := last.endByte
}

end SourceSpan

/-- A value paired with the exact source syntax that produced it. -/
structure Located (α : Type) where
  span : SourceSpan
  value : α
  deriving Repr, BEq, DecidableEq

namespace Located

def map {α β : Type} (f : α → β) (located : Located α) : Located β := {
  span := located.span
  value := f located.value
}

end Located

end Solcore.Surface
