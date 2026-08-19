import Solcore.Workspace.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- True exactly for a UTF-8 continuation byte. -/
def isUtf8ContinuationByte (byte : UInt8) : Bool :=
  0x80 <= byte && byte <= 0xbf

/--
True at either end of a string and at an interior UTF-8 scalar boundary.
The source is already a Lean `String`, so its byte encoding is valid UTF-8.
-/
def isUtf8Boundary (content : String) (offset : Nat) : Bool :=
  offset == 0 ||
    offset == content.utf8ByteSize ||
    match content.toByteArray.data[offset]? with
    | some byte => !isUtf8ContinuationByte byte
    | none => false

@[simp] theorem isUtf8Boundary_zero (content : String) :
    isUtf8Boundary content 0 = true := by
  simp [isUtf8Boundary]

@[simp] theorem isUtf8Boundary_end (content : String) :
    isUtf8Boundary content content.utf8ByteSize = true := by
  simp [isUtf8Boundary]

/-- A half-open UTF-8 byte range owned by one structured source identity. -/
structure SourceSpan where
  source : SourceId
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

namespace SourceSpan

/-- The byte length of a half-open span. -/
def length (span : SourceSpan) : Nat :=
  span.endByte - span.startByte

/-- Exact ownership, ordering, bounds, and UTF-8 boundary requirements. -/
def ValidFor (span : SourceSpan) (file : WorkspaceFile) : Prop :=
  span.source = file.id ∧
    span.startByte ≤ span.endByte ∧
    span.endByte ≤ file.content.utf8ByteSize ∧
    isUtf8Boundary file.content span.startByte = true ∧
    isUtf8Boundary file.content span.endByte = true

/-- Executable decision procedure for `ValidFor`. -/
def isValidFor (span : SourceSpan) (file : WorkspaceFile) : Bool :=
  decide (span.source = file.id) &&
    span.startByte ≤ span.endByte &&
    span.endByte ≤ file.content.utf8ByteSize &&
    isUtf8Boundary file.content span.startByte &&
    isUtf8Boundary file.content span.endByte

theorem isValidFor_eq_true_iff (span : SourceSpan) (file : WorkspaceFile) :
    span.isValidFor file = true ↔ span.ValidFor file := by
  simp [isValidFor, ValidFor, and_assoc]

/-- Declarative containment of one validly ordered half-open span by another. -/
def Contains (outer inner : SourceSpan) : Prop :=
  outer.source = inner.source ∧
    outer.startByte ≤ inner.startByte ∧
    inner.startByte ≤ inner.endByte ∧
    inner.endByte ≤ outer.endByte

/-- Executable decision procedure for `Contains`. -/
def contains (outer inner : SourceSpan) : Bool :=
  decide (outer.source = inner.source) &&
    outer.startByte ≤ inner.startByte &&
    inner.startByte ≤ inner.endByte &&
    inner.endByte ≤ outer.endByte

theorem contains_eq_true_iff (outer inner : SourceSpan) :
    outer.contains inner = true ↔ outer.Contains inner := by
  simp [contains, Contains, and_assoc]

/--
The endpoint cover of two spans. Callers establish shared ownership and source
order before using this constructor as a semantic cover.
-/
def cover (first last : SourceSpan) : SourceSpan := {
  source := first.source
  startByte := first.startByte
  endByte := last.endByte
}

end SourceSpan

/-- A value paired with the exact source range that produced it. -/
structure Located (α : Type) where
  span : SourceSpan
  payload : α
  deriving Repr, BEq, DecidableEq

namespace Located

/-- Map a located payload without changing its source range. -/
def map {α β : Type} (f : α → β) (located : Located α) : Located β := {
  span := located.span
  payload := f located.payload
}

@[simp] theorem map_span {α β : Type} (f : α → β) (located : Located α) :
    (located.map f).span = located.span :=
  rfl

@[simp] theorem map_payload {α β : Type} (f : α → β)
    (located : Located α) :
    (located.map f).payload = f located.payload :=
  rfl

end Located

end Solcore.Surface.Multi
