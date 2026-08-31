import Solcore.Workspace.Syntax

set_option autoImplicit false

namespace Solcore.Syntax

open Solcore.Workspace

/-- True exactly when a byte can occur only as a UTF-8 continuation byte. -/
def isUtf8ContinuationByte (byte : UInt8) : Bool :=
  0x80 <= byte && byte <= 0xbf

/--
True at the beginning or end of a source and at every interior UTF-8 scalar
boundary. A Lean `String` already contains valid UTF-8.
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

/-- A half-open UTF-8 byte range in one validated workspace source. -/
structure SourceSpan where
  source : SourceId
  startByte : Nat
  endByte : Nat
  deriving Repr, BEq, DecidableEq

namespace SourceSpan

/-- Length of the half-open byte range. Invalid reversed spans have length 0. -/
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

/-- Declarative containment of a half-open span by another source-owned span. -/
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

/-- The exact span of all UTF-8 bytes in a source. -/
def fullFile (file : WorkspaceFile) : SourceSpan := {
  source := file.id
  startByte := 0
  endByte := file.content.utf8ByteSize
}

@[simp] theorem fullFile_validFor (file : WorkspaceFile) :
    (fullFile file).ValidFor file := by
  simp [fullFile, ValidFor]

theorem fullFile_contains_of_validFor {file : WorkspaceFile}
    {span : SourceSpan} (valid : span.ValidFor file) :
    (fullFile file).Contains span := by
  rcases valid with ⟨owned, ordered, bounded, _startBoundary, _endBoundary⟩
  exact ⟨owned.symm, Nat.zero_le _, ordered, bounded⟩

/-- Cover two ordered spans known by the caller to belong to one source. -/
def cover (first last : SourceSpan) : SourceSpan := {
  source := first.source
  startByte := first.startByte
  endByte := last.endByte
}

end SourceSpan

/-- A syntax value paired with the exact source range that produced it. -/
structure Located (α : Type) where
  span : SourceSpan
  value : α
  deriving Repr, BEq, DecidableEq

namespace Located

/-- Map a located value without changing its source range. -/
def map {α β : Type} (f : α → β) (located : Located α) : Located β := {
  span := located.span
  value := f located.value
}

@[simp] theorem map_span {α β : Type} (f : α → β) (located : Located α) :
    (located.map f).span = located.span :=
  rfl

@[simp] theorem map_value {α β : Type} (f : α → β)
    (located : Located α) :
    (located.map f).value = f located.value :=
  rfl

end Located

/-- Exact source spelling paired with its range. -/
abbrev SpannedText := Located String

/-- Source comment form retained as parser trivia. -/
inductive CommentKind where
  | line
  | block
  deriving Repr, BEq, DecidableEq

/-- Comment text excludes its outer delimiter; its span includes the delimiter. -/
structure Comment where
  kind : CommentKind
  text : String
  span : SourceSpan
  deriving Repr, BEq, DecidableEq

end Solcore.Syntax
