import Solcore.Syntax.Source

set_option autoImplicit false

namespace Solcore.Syntax

/-- Source-ordered, nonempty spans whose provenance is valid for one file. -/
def SpanSequence.ValidFor {α : Type} (file : SourceFile)
    (spanOf : α → SourceSpan) : Nat → List α → Prop
  | _, [] => True
  | previousEnd, item :: rest =>
      (spanOf item).ValidFor file ∧
        previousEnd ≤ (spanOf item).startByte ∧
        (spanOf item).startByte < (spanOf item).endByte ∧
        SpanSequence.ValidFor file spanOf (spanOf item).endByte rest

namespace SpanSequence.ValidFor

/--
Build a valid sequence from pointwise span laws and written-order
nonoverlap, including the incoming boundary before the first item.
-/
theorem of_forall_pairwise {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (spanValid : ∀ item ∈ items, (spanOf item).ValidFor file)
    (afterPrevious : ∀ item ∈ items,
      previousEnd ≤ (spanOf item).startByte)
    (spanNonempty : ∀ item ∈ items,
      (spanOf item).startByte < (spanOf item).endByte)
    (ordered : items.Pairwise fun left right =>
      (spanOf left).endByte ≤ (spanOf right).startByte) :
    SpanSequence.ValidFor file spanOf previousEnd items := by
  induction items generalizing previousEnd with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      cases ordered with
      | cons headBeforeTail tailOrdered =>
          refine ⟨spanValid head (by simp), afterPrevious head (by simp),
            spanNonempty head (by simp), ?_⟩
          apply inductionHypothesis
          · intro item member
            exact spanValid item (List.mem_cons_of_mem head member)
          · exact headBeforeTail
          · intro item member
            exact spanNonempty item (List.mem_cons_of_mem head member)
          · exact tailOrdered

/-- Every member of a valid sequence has valid source provenance. -/
theorem span_valid {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (valid : SpanSequence.ValidFor file spanOf previousEnd items)
    {item : α} (member : item ∈ items) :
    (spanOf item).ValidFor file := by
  induction items generalizing previousEnd with
  | nil => contradiction
  | cons head tail ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with ⟨headValid, _afterPrevious, _nonempty, tailValid⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact headValid
      · exact ih tailValid member

/-- Every member begins at or after the sequence's incoming byte boundary. -/
theorem previousEnd_le_start {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (valid : SpanSequence.ValidFor file spanOf previousEnd items)
    {item : α} (member : item ∈ items) :
    previousEnd ≤ (spanOf item).startByte := by
  induction items generalizing previousEnd with
  | nil => contradiction
  | cons head tail ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨_headValid, afterPrevious, headNonempty, tailValid⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact afterPrevious
      · exact Nat.le_trans
          (Nat.le_trans afterPrevious (Nat.le_of_lt headNonempty))
          (ih tailValid member)

/-- Every member of a validated lexer sequence has a nonempty span. -/
theorem span_nonempty {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (valid : SpanSequence.ValidFor file spanOf previousEnd items)
    {item : α} (member : item ∈ items) :
    (spanOf item).startByte < (spanOf item).endByte := by
  induction items generalizing previousEnd with
  | nil => contradiction
  | cons head tail ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨_headValid, _afterPrevious, headNonempty, tailValid⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact headNonempty
      · exact ih tailValid member

/-- Sequence order implies pairwise nonoverlap in written order. -/
theorem pairwise_nonoverlap {α : Type} {file : SourceFile}
    {spanOf : α → SourceSpan} {previousEnd : Nat} {items : List α}
    (valid : SpanSequence.ValidFor file spanOf previousEnd items) :
    items.Pairwise fun left right =>
      (spanOf left).endByte ≤ (spanOf right).startByte := by
  induction items generalizing previousEnd with
  | nil => exact .nil
  | cons head tail ih =>
      simp only [SpanSequence.ValidFor] at valid
      rcases valid with
        ⟨_headValid, _afterPrevious, _headNonempty, tailValid⟩
      apply List.Pairwise.cons
      · intro item member
        exact tailValid.previousEnd_le_start member
      · exact ih tailValid

end SpanSequence.ValidFor

end Solcore.Syntax
