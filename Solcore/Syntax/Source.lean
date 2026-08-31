set_option autoImplicit false

namespace Solcore.Syntax

/-- Logical source owner, independent of the spelling of a module path. -/
inductive SourceOrigin where
  | main
  | standard
  | external (name : String)
  deriving Repr, BEq, DecidableEq

/--
Stable identity of one canonical source. `path` is retained verbatim here;
workspace construction will separately validate the `.sol` path policy.
-/
structure SourceId where
  origin : SourceOrigin
  path : String
  deriving Repr, BEq, DecidableEq

/-- One canonical source file presented to the lexer or parser. -/
structure SourceFile where
  id : SourceId
  content : String
  deriving Repr, BEq, DecidableEq

namespace SourceFile

/-- Number of UTF-8 content bytes charged to this source. -/
def sourceBytes (file : SourceFile) : Nat :=
  file.content.utf8ByteSize

end SourceFile

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
def ValidFor (span : SourceSpan) (file : SourceFile) : Prop :=
  span.source = file.id ∧
    span.startByte ≤ span.endByte ∧
    span.endByte ≤ file.content.utf8ByteSize ∧
    isUtf8Boundary file.content span.startByte = true ∧
    isUtf8Boundary file.content span.endByte = true

/-- Executable decision procedure for `ValidFor`. -/
def isValidFor (span : SourceSpan) (file : SourceFile) : Bool :=
  decide (span.source = file.id) &&
    span.startByte ≤ span.endByte &&
    span.endByte ≤ file.content.utf8ByteSize &&
    isUtf8Boundary file.content span.startByte &&
    isUtf8Boundary file.content span.endByte

theorem isValidFor_eq_true_iff (span : SourceSpan) (file : SourceFile) :
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
def fullFile (file : SourceFile) : SourceSpan := {
  source := file.id
  startByte := 0
  endByte := file.content.utf8ByteSize
}

@[simp] theorem fullFile_validFor (file : SourceFile) :
    (fullFile file).ValidFor file := by
  simp [fullFile, ValidFor]

theorem fullFile_contains_of_validFor {file : SourceFile}
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

/-- Covering two valid endpoints yields a valid span when they are ordered. -/
theorem cover_validFor {file : SourceFile} {first last : SourceSpan}
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (ordered : first.startByte ≤ last.endByte) :
    (cover first last).ValidFor file := by
  rcases firstValid with
    ⟨firstOwned, _firstOrdered, _firstBounded,
      firstStartBoundary, _firstEndBoundary⟩
  rcases lastValid with
    ⟨_lastOwned, _lastOrdered, lastBounded,
      _lastStartBoundary, lastEndBoundary⟩
  exact ⟨firstOwned, ordered, lastBounded,
    firstStartBoundary, lastEndBoundary⟩

/-- An ordered cover contains its first endpoint span. -/
theorem cover_contains_first {file : SourceFile} {first last : SourceSpan}
    (firstValid : first.ValidFor file)
    (endOrdered : first.endByte ≤ last.endByte) :
    (cover first last).Contains first := by
  rcases firstValid with
    ⟨_firstOwned, firstOrdered, _firstBounded,
      _firstStartBoundary, _firstEndBoundary⟩
  exact ⟨rfl, Nat.le_refl _, firstOrdered, endOrdered⟩

/-- An ordered cover contains its last endpoint span. -/
theorem cover_contains_last {file : SourceFile} {first last : SourceSpan}
    (firstValid : first.ValidFor file) (lastValid : last.ValidFor file)
    (startOrdered : first.startByte ≤ last.startByte) :
    (cover first last).Contains last := by
  rcases firstValid with
    ⟨firstOwned, _firstOrdered, _firstBounded,
      _firstStartBoundary, _firstEndBoundary⟩
  rcases lastValid with
    ⟨lastOwned, lastOrdered, _lastBounded,
      _lastStartBoundary, _lastEndBoundary⟩
  exact ⟨firstOwned.trans lastOwned.symm, startOrdered,
    lastOrdered, Nat.le_refl _⟩

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
