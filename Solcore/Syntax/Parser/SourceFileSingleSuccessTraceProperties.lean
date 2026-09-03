import Solcore.Syntax.Parser.FileItemStrictProperties

/-! Executable composition for one successful top-level item reaching the end.
The item reply is an explicit premise, not an independent grammar derivation.
The wrapper adds no diagnostics and retains the item's complete final trace. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- One item step and one end check preserve the reverse item prefix in source
order. Existing production contracts supply strict progress and window identity. -/
theorem parseItems_singleSuccessToEnd_exact
    (fuel : Nat) (itemsRev : List TopItem)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (fuel + 2) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics := by
  have progress := parseItemsItem_cursor_lt_onSuccess parsed
  have inside : input.cursor < input.window.endIndex := by
    simpa only [atEnd] using progress
  have shape := parseItemsItem_complete_contract.preservesTokenWindow input
  rw [parsed] at shape
  have windowEq : next.window = input.window := shape.2
  have inputNotAtEnd : input.atEnd = false := by
    simp only [State.atEnd]
    exact decide_eq_false (Nat.not_le_of_gt inside)
  have nextAtEnd : next.atEnd = true := by
    simp [State.atEnd, windowEq, atEnd]
  refine ⟨next, ?_, rfl, rfl⟩
  simp [parseItems, inputNotAtEnd, parsed, progress, nextAtEnd, List.reverse_cons]

/-- Strict item progress makes the production fuel sufficient for the item
step and final end check, with no input-validity or diagnostic-free premise. -/
theorem parseItems_production_singleSuccessToEnd_exact
    (itemsRev : List TopItem) {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics := by
  have inside : input.cursor < input.window.endIndex := by
    simpa only [atEnd] using parseItemsItem_cursor_lt_onSuccess parsed
  have positive : 0 < input.remainingCount := by
    simp only [State.remainingCount]
    omega
  obtain ⟨fuel, fuelEq⟩ : ∃ fuel, input.remainingCount = fuel + 1 :=
    ⟨input.remainingCount - 1, by omega⟩
  simpa only [fuelEq, Nat.add_assoc] using
    parseItems_singleSuccessToEnd_exact fuel itemsRev parsed atEnd

/-- A successful item reaching the window end becomes the exact singleton
comment-attached file. All prior and newly produced item diagnostics are kept;
this wrapper neither clears the trace nor emits an extra event. -/
theorem sourceFile_singleSuccessToEnd_exact (comments : List Comment)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics := by
  rcases parseItems_production_singleSuccessToEnd_exact [] parsed atEnd with
    ⟨output, result, remainderEq, traceEq⟩
  refine ⟨output, ?_, remainderEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, List.nil_append, result,
    List.map_cons, List.map_nil]

end Solcore.Syntax.Parser.FileInternals
