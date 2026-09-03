import Solcore.Syntax.Parser.SourceFileSingleRecoveryTraceProperties

/-! Exact raw diagnostics at the recognized-start file boundary. Unlike a
transactional retry, this cursor rewind retains diagnostics of the failed
attempt, then appends its complete expectation failure. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- A rejected recognized start stops the file loop without adding an item.
Earlier failed-attempt diagnostics precede its newly committed failure report. -/
theorem parseItems_boundaryStop_trace_exact (fuel : Nat) (itemsRev : List TopItem)
    {input failed : State} {failure : Failure}
    (inside : input.cursor < input.window.endIndex)
    (starts : atTopItemStart input = true)
    (rejected : parseItemsItem input = .reject failure failed) :
    ∃ output, parseItems (fuel + 1) itemsRev input = .ok itemsRev.reverse output ∧
      output.declarativeRemainder =
        { failed.declarativeRemainder with cursor := input.cursor } ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  let rewound := { failed with cursor := input.cursor }
  refine ⟨rewound.emit failure.toDiagnostic, ?_, rfl, ?_⟩
  · have notAtEnd : input.atEnd = false := by
      simp only [State.atEnd]
      exact decide_eq_false (Nat.not_le_of_gt inside)
    simp only [parseItems, notAtEnd, Bool.false_eq_true, ↓reduceIte, rejected, starts]
    rfl
  · simp only [State.diagnostics, State.emit, rewound, List.reverse_cons]

/-- The production source-file wrapper retains comments and an empty item list
at a recognized-start rejection, with the exact committed raw diagnostic trace. -/
theorem sourceFile_boundaryStop_trace_exact (comments : List Comment)
    {input failed : State} {failure : Failure}
    (inside : input.cursor < input.window.endIndex)
    (starts : atTopItemStart input = true)
    (rejected : parseItemsItem input = .reject failure failed) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := []
        comments
      } output ∧
      output.declarativeRemainder =
        { failed.declarativeRemainder with cursor := input.cursor } ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  rcases parseItems_boundaryStop_trace_exact input.remainingCount [] inside starts rejected with
    ⟨output, result, remainderEq, traceEq⟩
  refine ⟨output, ?_, remainderEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, result, List.map_nil]

end Solcore.Syntax.Parser.FileInternals
