import Solcore.Syntax.Lexer.Character

set_option autoImplicit false

namespace Solcore.Syntax

set_option maxRecDepth 4096 in
private theorem utf8FirstByte_not_continuation (byte : UInt8)
    (first : byte.IsUTF8FirstByte) :
    isUtf8ContinuationByte byte = false := by
  have checked : ∀ value : Fin 256,
      (UInt8.ofNat value.val).IsUTF8FirstByte →
        isUtf8ContinuationByte (UInt8.ofNat value.val) = false := by decide
  have checkedByte : byte.IsUTF8FirstByte → isUtf8ContinuationByte byte = false := by
    simpa only [UInt8.ofNat_toNat] using checked ⟨byte.toNat, byte.toNat_lt⟩
  exact checkedByte first

/-- The end of a string prefix is a boundary in the appended source. -/
theorem isUtf8Boundary_append_left (leading trailing : String) :
    isUtf8Boundary (leading ++ trailing) leading.utf8ByteSize = true := by
  have valid : leading.rawEndPos.IsValid (leading ++ trailing) :=
    String.Pos.Raw.isValid_rawEndPos.append_right trailing
  unfold isUtf8Boundary
  by_cases zero : leading.utf8ByteSize = 0
  · rw [zero]
    rfl
  by_cases ending :
      leading.utf8ByteSize = (leading ++ trailing).utf8ByteSize
  · rw [ending]
    have self :
        ((leading ++ trailing).utf8ByteSize ==
          (leading ++ trailing).utf8ByteSize) = true :=
      beq_iff_eq.mpr rfl
    rw [self]
    cases (leading ++ trailing).utf8ByteSize == 0 <;> rfl
  · have zeroBeq : (leading.utf8ByteSize == 0) = false :=
      beq_eq_false_iff_ne.mpr zero
    have endingBeq :
        (leading.utf8ByteSize ==
          (leading ++ trailing).utf8ByteSize) = false :=
      beq_eq_false_iff_ne.mpr ending
    rw [zeroBeq, endingBeq]
    simp only [Bool.false_or]
    have strict : leading.rawEndPos < (leading ++ trailing).rawEndPos := by
      simp only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos]
      exact Nat.lt_of_le_of_ne valid.le_utf8ByteSize ending
    have first :=
      (String.Pos.Raw.isValid_iff_isUTF8FirstByte.mp valid).resolve_left
        (fun equal => ending (String.Pos.Raw.ext_iff.mp equal))
    obtain ⟨_, firstByte⟩ := first
    have notContinuation := utf8FirstByte_not_continuation _ firstByte
    have byteBound :
        leading.utf8ByteSize <
          (leading ++ trailing).toByteArray.data.size := by
      simpa [String.Pos.Raw.lt_iff] using strict
    rw [show (leading ++ trailing).toByteArray.data[leading.utf8ByteSize]? =
        some ((leading ++ trailing).getUTF8Byte leading.rawEndPos strict) by
      rw [Array.getElem?_eq_getElem byteBound]
      rfl]
    simp [notContinuation]

namespace Lexer

/-- A lexer cursor identifies the byte end of an exact source prefix. -/
inductive CursorSuffix (file : SourceFile) (cursor : Nat)
    (remaining : List Char) : Prop where
  | intro
      (leading : List Char)
      (source_eq : file.content.toList = leading ++ remaining)
      (cursor_eq : cursor = byteSize leading)

namespace CursorSuffix

/-- The initial cursor is the empty prefix of its source. -/
theorem initial (file : SourceFile) :
    CursorSuffix file 0 file.content.toList := by
  exact ⟨[], by simp, by simp⟩

/-- The source bytes split exactly at every reached cursor. -/
theorem remainingByteSize {file : SourceFile} {cursor : Nat}
    {remaining : List Char} (suffix : CursorSuffix file cursor remaining) :
    file.content.utf8ByteSize = cursor + byteSize remaining := by
  rcases suffix with ⟨leading, sourceEq, cursorEq⟩
  rw [← byteSize_toList file.content, sourceEq, byteSize_append,
    cursorEq]

/-- Every exact character-prefix cursor lies on a UTF-8 boundary. -/
theorem boundary {file : SourceFile} {cursor : Nat}
    {remaining : List Char} (suffix : CursorSuffix file cursor remaining) :
    isUtf8Boundary file.content cursor = true := by
  rcases suffix with ⟨leading, sourceEq, cursorEq⟩
  have contentEq :
      file.content = String.ofList leading ++ String.ofList remaining := by
    calc
      file.content = String.ofList file.content.toList :=
        String.ofList_toList.symm
      _ = String.ofList (leading ++ remaining) := by rw [sourceEq]
      _ = String.ofList leading ++ String.ofList remaining := by
        rw [String.ofList_append]
  rw [contentEq, cursorEq]
  exact isUtf8Boundary_append_left _ _

/-- Consuming an exact prefix produces the corresponding next cursor. -/
theorem advancePrefix {file : SourceFile} {cursor : Nat}
    {input consumed remaining : List Char}
    (suffix : CursorSuffix file cursor input)
    (partition : input = consumed ++ remaining) :
    CursorSuffix file (cursor + byteSize consumed) remaining := by
  rcases suffix with ⟨leading, sourceEq, cursorEq⟩
  refine ⟨leading ++ consumed, ?_, ?_⟩
  · rw [sourceEq, partition, List.append_assoc]
  · rw [byteSize_append, cursorEq]

/-- A scanner progress witness preserves the exact cursor suffix. -/
theorem advance {file : SourceFile} {startByte endByte : Nat}
    {input remaining : List Char}
    (suffix : CursorSuffix file startByte input)
    (progress : Advances startByte input endByte remaining) :
    CursorSuffix file endByte remaining := by
  rcases progress with ⟨consumed, partition, rfl⟩
  exact suffix.advancePrefix partition

/-- An exact scanner transition always constructs a valid source span. -/
theorem sourceSpan_validFor {file : SourceFile} {startByte endByte : Nat}
    {input remaining : List Char}
    (suffix : CursorSuffix file startByte input)
    (progress : Advances startByte input endByte remaining) :
    (sourceSpan file startByte endByte).ValidFor file := by
  rcases progress with ⟨consumed, partition, endEq⟩
  have next : CursorSuffix file endByte remaining := by
    rw [endEq]
    exact suffix.advancePrefix partition
  refine ⟨rfl, ?_, ?_, suffix.boundary, next.boundary⟩
  · rw [endEq]
    exact Nat.le_add_right _ _
  rw [next.remainingByteSize]
  exact Nat.le_add_right _ _

end CursorSuffix

end Lexer

end Solcore.Syntax
