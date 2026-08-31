import Solcore.Syntax.Declaration

set_option autoImplicit false

namespace Solcore.Syntax

/-- Closed lexical failure catalog of the canonical source lexer. -/
inductive LexicalErrorKind where
  | invalidToken
  | unterminatedBlockComment
  | invalidStringEscape
  | internalFuelExhausted
  deriving Repr, BEq, DecidableEq

/-- One deterministic lexical failure at its exact source range. -/
structure LexicalDiagnostic where
  span : SourceSpan
  kind : LexicalErrorKind
  deriving Repr, BEq, DecidableEq

/-- Successful lexical output in source order. Comments are parser trivia. -/
structure LexedFile where
  source : SourceId
  tokens : List Token
  comments : List Comment
  diagnostics : List LexicalDiagnostic
  deriving Repr, BEq, DecidableEq

/--
Total public result. Ordinary lexical errors are accumulated in `LexedFile`;
the exceptional branch is reserved for an internal executor invariant.
-/
abbrev LexResult := Except LexicalDiagnostic LexedFile

namespace Lexer

/-- Construct a half-open span owned by the source being scanned. -/
def sourceSpan (file : SourceFile) (startByte endByte : Nat) : SourceSpan := {
  source := file.id
  startByte
  endByte
}

/-- UTF-8 byte size of an executor character slice. -/
def byteSize (characters : List Char) : Nat :=
  (String.ofList characters).utf8ByteSize

@[simp] theorem byteSize_nil : byteSize [] = 0 := by
  simp [byteSize]

theorem byteSize_cons (character : Char) (characters : List Char) :
    byteSize (character :: characters) =
      character.utf8Size + byteSize characters := by
  simp [byteSize, String.ofList_cons]

theorem byteSize_append (leading trailing : List Char) :
    byteSize (leading ++ trailing) =
      byteSize leading + byteSize trailing := by
  simp [byteSize, String.ofList_append]

@[simp] theorem byteSize_toList (text : String) :
    byteSize text.toList = text.utf8ByteSize := by
  simp [byteSize]

/-- A scanner consumes an exact character prefix and advances by its bytes. -/
def Advances (startByte : Nat) (input : List Char)
    (endByte : Nat) (remaining : List Char) : Prop :=
  ∃ consumed,
    input = consumed ++ remaining ∧
      endByte = startByte + byteSize consumed

/-- Prefix one consumed character to an exact scanner transition. -/
theorem Advances.prepend (character : Char)
    {startByte endByte : Nat} {input remaining : List Char}
    (progress : Advances (startByte + character.utf8Size)
      input endByte remaining) :
    Advances startByte (character :: input) endByte remaining := by
  rcases progress with ⟨consumed, partition, endEq⟩
  refine ⟨character :: consumed, by simp [partition], ?_⟩
  rw [byteSize_cons]
  simpa [Nat.add_assoc] using endEq

/-- Consuming one character advances by exactly its UTF-8 byte size. -/
theorem Advances.single (character : Char)
    (startByte : Nat) (remaining : List Char) :
    Advances startByte (character :: remaining)
      (startByte + character.utf8Size) remaining := by
  refine ⟨[character], by simp, ?_⟩
  simp [byteSize_cons]

/-- The executable lexer performs at most one main transition per character. -/
def fuelBound (file : SourceFile) : Nat :=
  file.content.length + 1

end Lexer

end Solcore.Syntax
