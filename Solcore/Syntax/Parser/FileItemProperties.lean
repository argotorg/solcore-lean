import Solcore.Syntax.Parser.DeriveCarrierProperties
import Solcore.Syntax.Parser.DeriveValidityProperties
import Solcore.Syntax.Parser.FilePlainTopItemProperties

/-! Contract for one derive-aware top-level item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem derive_start_le_item_end
    (plain : TopItemParserContract plainTopItem)
    {input afterDerive next : State} {derive : DeriveAttribute}
    {item : TopItem} (inputValid : input.ValidFor)
    (deriveResult : deriveAttribute input = .ok derive afterDerive)
    (itemResult : plainTopItem afterDerive = .ok item next)
    (itemSpanValid : item.span.ValidFor input.file) :
    derive.span.startByte ≤ item.span.endByte := by
  rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
    ⟨first, firstFound, firstStart⟩
  rcases plain.startsAtCurrentTokenOnSuccess _ _ _ itemResult with
    ⟨last, lastFound, lastStart⟩
  have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have lastAt := State.getElem?_eq_some_of_peek?_eq_some lastFound
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt firstAt
    (by simpa [deriveAttribute_preservesTokensOnSuccess _ _ _ deriveResult]
      using lastAt) (deriveAttribute_cursor_lt_onSuccess deriveResult)
  exact calc
    derive.span.startByte = first.span.startByte := firstStart.symm
    _ ≤ first.span.endByte := (inputValid.peek?_span_validFor firstFound).2.1
    _ ≤ last.span.startByte := separated
    _ = item.span.startByte := lastStart
    _ ≤ item.span.endByte := itemSpanValid.2.1

/-- The parser used by the file-item loop preserves canonical top-item
provenance through both plain and derive-aware paths. -/
theorem parseItemsItem_contract (contract : ContractDeclInputs) :
    TopItemParserContract parseItemsItem := by
  have plain := plainTopItem_contract contract
  constructor
  · intro input inputValid
    unfold parseItemsItem topItem
    by_cases attributed : isSymbol input .hash
    · simp only [attributed, if_true]
      have deriveReply := deriveAttribute_validFor input inputValid
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveReply
          simpa only [Reply.ValidFor] using deriveReply
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveReply
          have itemReply := plain.validFor afterDerive deriveReply.2.1
          cases itemResult : plainTopItem afterDerive with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              simp only
              rw [itemResult] at itemReply
              exact itemReply.of_file_eq deriveReply.2.2
          | ok item next =>
              simp only
              rw [itemResult] at itemReply
              have fileEq := itemReply.2.2.trans deriveReply.2.2
              have attached := attachDeriveAttribute_reply_validFor derive item
                next itemReply.2.1 (by simpa [fileEq] using deriveReply.1)
                (by simpa [itemReply.2.2] using itemReply.1)
                (derive_start_le_item_end plain inputValid deriveResult itemResult
                  (by simpa [deriveReply.2.2] using
                    itemReply.1.validFor.span_valid))
              exact attached.of_file_eq fileEq
    · simp only [attributed]
      exact plain.validFor input inputValid
  · intro input
    unfold parseItemsItem topItem
    split
    · have deriveWindow := deriveAttribute_preservesTokenWindow input
      cases deriveResult : deriveAttribute input with
      | invariant error => simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          simp only
          rw [deriveResult] at deriveWindow
          simpa only [Reply.PreservesTokenWindow] using deriveWindow
      | ok derive afterDerive =>
          simp only
          rw [deriveResult] at deriveWindow
          have itemWindow := plain.preservesTokenWindow afterDerive
          cases itemResult : plainTopItem afterDerive with
          | invariant error => simp only [Reply.PreservesTokenWindow]
          | reject failure rejected =>
              simp only
              rw [itemResult] at itemWindow
              exact itemWindow.trans deriveWindow
          | ok item next =>
              simp only
              rw [itemResult] at itemWindow
              exact (attachDeriveAttribute_preservesTokenWindow derive item next).trans
                (itemWindow.trans deriveWindow)
    · exact plain.preservesTokenWindow input
  · intro input result final parsed
    unfold parseItemsItem topItem at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
      rename_i item next
      exact Nat.le_trans
        (deriveAttribute_cursorMonotoneOnSuccess _ _ _ deriveResult)
        (Nat.le_trans (plain.cursorMonotoneOnSuccess _ _ _ itemResult)
          (attachDeriveAttribute_cursorMonotoneOnSuccess _ _ _ _ _ parsed))
    · exact plain.cursorMonotoneOnSuccess _ _ _ parsed
  · intro input result final parsed
    unfold parseItemsItem topItem at parsed
    split at parsed
    · cases deriveResult : deriveAttribute input <;> simp [deriveResult] at parsed
      rename_i derive afterDerive
      cases itemResult : plainTopItem afterDerive <;> simp [itemResult] at parsed
      rcases deriveAttribute_startsAtCurrentTokenOnSuccess _ _ _ deriveResult with
        ⟨token, found, start⟩
      exact ⟨token, found, start.trans
        (attachDeriveAttribute_preservesDeriveStartOnSuccess _ _ parsed)⟩
    · exact plain.startsAtCurrentTokenOnSuccess _ _ _ parsed

end Solcore.Syntax.Parser.FileInternals
