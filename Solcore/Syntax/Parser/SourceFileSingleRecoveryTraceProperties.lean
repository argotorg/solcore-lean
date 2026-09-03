import Solcore.Syntax.Parser.TopItemRecoveryTraceProperties
import Solcore.Syntax.Parser.TopItemUnrecognizedTraceProperties

/-! A single independent recovery-to-end derivation fixes the raw file AST
and diagnostic trace, with no executable-success premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem recoveryScan_item_eq_error
    {first last : SourceSpan} {input after : DeclarativeGrammar.Remainder}
    {item : TopItem}
    (scan : DeclarativeGrammar.TopItemRecoveryScanParses first last input item after) :
    item = { span := item.span, leadingComments := [], value := .error } := by
  induction scan with
  | stop => rfl
  | next _ _ _ ih => exact ih

/-- Independent recovery always constructs the exact error-item variant with
empty parser-time comments; its source span is retained in the result. -/
theorem recoveredTopItem_eq_error
    {input after : DeclarativeGrammar.Remainder} {item : TopItem}
    (recovered : DeclarativeGrammar.TopItemRecoveryParses input item after) :
    item = { span := item.span, leadingComments := [], value := .error } := by
  cases recovered with
  | recovered _ scan => exact recoveryScan_item_eq_error scan

private theorem recovery_input_cursor_lt_end
    {input : State} {item : TopItem} {after : DeclarativeGrammar.Remainder}
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item after) :
    input.cursor < input.window.endIndex := by
  cases recovered with
  | recovered current _ => exact current.1

/-- Two outer loop steps suffice when an unrecognized first item recovers to
the end: one recovery step and one end check. The rejected inner failure is
not emitted, and the existing reverse accumulator is retained in order. -/
theorem parseItems_singleRecoveryToEnd_exact
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {item : TopItem} {after : DeclarativeGrammar.Remainder}
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item after)
    (atEnd : after.cursor = input.window.endIndex) :
    ∃ output, parseItems (fuel + 2) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++
        [{ span := item.span, kind := .recovered .topItem }] := by
  rcases recoverTopItem_ordinary_success_iff_with_trace.mp recovered with
    ⟨output, recoveryResult, outputEq, traceEq⟩
  have windowEq := recoverTopItem_preservesTokenWindow input
  rw [recoveryResult] at windowEq
  have cursorEq : output.cursor = after.cursor := congrArg (·.cursor) outputEq
  have outputAtEnd : output.atEnd = true := by
    simp only [State.atEnd]
    apply decide_eq_true
    rw [windowEq.2, cursorEq, atEnd]
    exact Nat.le_refl _
  have inputNotAtEnd : input.atEnd = false := by
    simp only [State.atEnd]
    exact decide_eq_false (Nat.not_le_of_gt (recovery_input_cursor_lt_end recovered))
  have noBoundary := atTopItemStart_eq_false_of_topItemStartAbsent startsAbsent
  have itemRejected := parseItemsItem_eq_rejectAt_of_topItemStartAbsent startsAbsent
  refine ⟨output, ?_, outputEq, traceEq⟩
  simp [parseItems, inputNotAtEnd, itemRejected, rejectAt, noBoundary,
    recoveryResult, outputAtEnd, List.reverse_cons]

/-- The mandatory first recovery token makes the production fuel sufficient
for the recovery step followed by the final end check. -/
theorem parseItems_production_singleRecoveryToEnd_exact (itemsRev : List TopItem)
    {input : State} {item : TopItem} {after : DeclarativeGrammar.Remainder}
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item after)
    (atEnd : after.cursor = input.window.endIndex) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++
        [{ span := item.span, kind := .recovered .topItem }] := by
  have inside := recovery_input_cursor_lt_end recovered
  have positive : 0 < input.remainingCount := by
    simp only [State.remainingCount]
    omega
  obtain ⟨fuel, fuelEq⟩ : ∃ fuel, input.remainingCount = fuel + 1 :=
    ⟨input.remainingCount - 1, by omega⟩
  simpa only [fuelEq, Nat.add_assoc] using
    parseItems_singleRecoveryToEnd_exact fuel itemsRev startsAbsent recovered atEnd

/-- Independent absence of top-item starts and one recovery-to-end derivation
fix the singleton comment-attached error item and exact raw diagnostic suffix.
No validity premise is needed for this syntax-and-trace-only correspondence. -/
theorem sourceFile_singleRecoveryToEnd_exact (comments : List Comment)
    {input : State} {item : TopItem} {after : DeclarativeGrammar.Remainder}
    (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
    (recovered : DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item after)
    (atEnd : after.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++
        [{ span := item.span, kind := .recovered .topItem }] := by
  rcases parseItems_production_singleRecoveryToEnd_exact [] startsAbsent recovered
      atEnd with ⟨output, loopResult, outputEq, traceEq⟩
  refine ⟨output, ?_, outputEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, List.nil_append, loopResult,
    List.map_cons, List.map_nil]

end Solcore.Syntax.Parser.FileInternals
