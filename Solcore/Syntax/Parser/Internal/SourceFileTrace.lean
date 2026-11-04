import Solcore.Syntax.Parser.Internal.SourceFileSoundness
import Solcore.Syntax.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.FileProofs
import Solcore.Syntax.Internal.TraceBasics
import Solcore.Syntax.Parser.Internal.TriviaProofs
import Solcore.Syntax.Parser.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.ParseProperties

/-!
Parser side of the traces of top items and source files: the parsers produce exactly the
events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemRecoveryTraceProperties
/-! Exact raw diagnostic effects of standalone top-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem advance?_diagnosticsRev_eq {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    next.diagnosticsRev = input.diagnosticsRev := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

/-- Finishing a recovery adds exactly its recovered-span diagnostic. -/
theorem finishRecoveredTopItem_success_diagnosticsRev_eq
    {first last : SourceSpan} {input output : State} {item : TopItem}
    (result : finishRecoveredTopItem first last input = .ok item output) :
    output.diagnosticsRev =
      { span := item.span, kind := .recovered .topItem } ::
        input.diagnosticsRev := by
  unfold finishRecoveredTopItem at result
  cases result
  rfl

/-- Scanning consumes tokens silently before adding one recovery diagnostic. -/
theorem recoverTopItemAux_success_diagnosticsRev_eq (first : SourceSpan) :
    ∀ fuel last input item output,
      recoverTopItemAux first last fuel input = .ok item output →
      output.diagnosticsRev =
        { span := item.span, kind := .recovered .topItem } ::
          input.diagnosticsRev := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input item output result
      simp [recoverTopItemAux] at result
  | succ fuel ih =>
      intro last input item output result
      unfold recoverTopItemAux at result
      split at result
      · exact finishRecoveredTopItem_success_diagnosticsRev_eq result
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            exact finishRecoveredTopItem_success_diagnosticsRev_eq result
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            simpa only [advance?_diagnosticsRev_eq advanced] using
              ih token.span next item output result

/-- The mandatory first token is silent; complete recovery adds one event. -/
theorem recoverTopItem_success_diagnosticsRev_eq
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnosticsRev =
      { span := item.span, kind := .recovered .topItem } ::
        input.diagnosticsRev := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      simpa only [advance?_diagnosticsRev_eq advanced] using
        recoverTopItemAux_success_diagnosticsRev_eq token.span
          (next.remainingCount + 1) token.span next item output result

/-- Finishing recovery preserves prior forward-order diagnostics exactly. -/
theorem finishRecoveredTopItem_success_diagnostics_eq
    {first last : SourceSpan} {input output : State} {item : TopItem}
    (result : finishRecoveredTopItem first last input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    finishRecoveredTopItem_success_diagnosticsRev_eq result, List.reverse_cons]

/-- Auxiliary recovery has the same exact forward-order singleton effect. -/
theorem recoverTopItemAux_success_diagnostics_eq
    {first last : SourceSpan} {fuel : Nat} {input output : State}
    {item : TopItem}
    (result : recoverTopItemAux first last fuel input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    recoverTopItemAux_success_diagnosticsRev_eq first fuel last input item
      output result, List.reverse_cons]

/-- Standalone recovery appends exactly one diagnostic at its AST span. -/
theorem recoverTopItem_success_diagnostics_eq
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    output.diagnostics = input.diagnostics ++
      [{ span := item.span, kind := .recovered .topItem }] := by
  simp only [State.diagnostics,
    recoverTopItem_success_diagnosticsRev_eq result, List.reverse_cons]

/-- An unavailable first token rejects without modifying the diagnostics. -/
theorem recoverTopItem_reject_diagnosticsRev_eq
    {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnosticsRev = input.diagnosticsRev := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      rfl
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverTopItemAux_production_exists_ok token.span token.span next
          with ⟨item, final, recovered⟩
      rw [recovered] at result
      contradiction

/-- Rejection retains the complete prior forward-order diagnostic list. -/
theorem recoverTopItem_reject_diagnostics_eq
    {input output : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure output) :
    output.diagnostics = input.diagnostics := by
  simp only [State.diagnostics, recoverTopItem_reject_diagnosticsRev_eq result]

/-- Independent recovery success also fixes the exact added raw diagnostic. -/
theorem recoverTopItem_ordinary_success_iff_with_trace
    {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item remainder ↔
      ∃ output, recoverTopItem input = .ok item output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          [{ span := item.span, kind := .recovered .topItem }] := by
  constructor
  · intro parsed
    rcases recoverTopItem_ordinary_success_iff.mp parsed with
      ⟨output, result, after⟩
    exact ⟨output, result, after, recoverTopItem_success_diagnostics_eq result⟩
  · rintro ⟨output, result, after, _trace⟩
    exact recoverTopItem_ordinary_success_iff.mpr ⟨output, result, after⟩

/-- Independent recovery rejection corresponds to execution with no events. -/
theorem recoverTopItem_ordinary_reject_iff_with_trace
    {input : State} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder remainder ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics := by
  constructor
  · intro rejected
    rcases recoverTopItem_ordinary_reject_iff.mp rejected with
      ⟨failure, output, result, after⟩
    exact ⟨failure, output, result, after,
      recoverTopItem_reject_diagnostics_eq result⟩
  · rintro ⟨failure, output, result, after, _trace⟩
    exact recoverTopItem_ordinary_reject_iff.mpr ⟨failure, output, result, after⟩

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemRecoveryTraceCompletenessProperties
/-! Exact executable correspondence for independent top-item recovery traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Interpret span events at the fixed top-item recovery kind and site. -/
def topItemRecoveryDiagnostics (trace : List SourceSpan) : List ParseDiagnostic :=
  trace.map fun span => { span, kind := .recovered .topItem }

/-- No event span is lost when recovery events become diagnostics. -/
@[simp] theorem topItemRecoveryDiagnostics_spans (trace : List SourceSpan) :
    (topItemRecoveryDiagnostics trace).map ParseDiagnostic.span = trace := by
  simp [topItemRecoveryDiagnostics, List.map_map, Function.comp_def]

/-- The diagnostic interpretation preserves the complete event sequence. -/
theorem topItemRecoveryDiagnostics_injective :
    Function.Injective topItemRecoveryDiagnostics := by
  intro left right equal
  have spans := congrArg (List.map ParseDiagnostic.span) equal
  simpa only [topItemRecoveryDiagnostics_spans] using spans

/-- Independent recovery success is equivalent to execution with the same
AST, endpoint, and exact raw trace appended after prior diagnostics. -/
theorem recoverTopItem_trace_success_iff
    {input : State} {item : TopItem}
    {remainder : DeclarativeGrammar.Remainder} {trace : List SourceSpan} :
    DeclarativeGrammar.TopItemRecoveryTraceParses
      input.declarativeRemainder item remainder trace ↔
      ∃ output, recoverTopItem input = .ok item output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          topItemRecoveryDiagnostics trace := by
  rw [DeclarativeGrammar.topItemRecoveryTraceParses_iff]
  constructor
  · rintro ⟨parsed, rfl⟩
    simpa only [topItemRecoveryDiagnostics, List.map_cons, List.map_nil] using
      recoverTopItem_ordinary_success_iff_with_trace.mp parsed
  · rintro ⟨output, result, after, traceEq⟩
    refine ⟨recoverTopItem_ordinary_success_iff.mpr ⟨output, result, after⟩, ?_⟩
    have singleton := recoverTopItem_success_diagnostics_eq result
    have mapped : topItemRecoveryDiagnostics trace =
        topItemRecoveryDiagnostics [item.span] :=
      List.append_cancel_left (traceEq.symm.trans singleton)
    exact topItemRecoveryDiagnostics_injective mapped

/-- Independent recovery rejection is equivalent to the same rejected
endpoint and an empty appended trace, without fixing the failure payload. -/
theorem recoverTopItem_trace_reject_iff
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {trace : List SourceSpan} :
    DeclarativeGrammar.TopItemRecoveryTraceRejects
      input.declarativeRemainder remainder trace ↔
      ∃ failure output, recoverTopItem input = .reject failure output ∧
        output.declarativeRemainder = remainder ∧
        output.diagnostics = input.diagnostics ++
          topItemRecoveryDiagnostics trace := by
  rw [DeclarativeGrammar.topItemRecoveryTraceRejects_iff]
  constructor
  · rintro ⟨rejected, rfl⟩
    simpa only [topItemRecoveryDiagnostics, List.map_nil, List.append_nil] using
      recoverTopItem_ordinary_reject_iff_with_trace.mp rejected
  · rintro ⟨failure, output, result, after, traceEq⟩
    refine ⟨recoverTopItem_ordinary_reject_iff.mpr
      ⟨failure, output, result, after⟩, ?_⟩
    have unchanged := recoverTopItem_reject_diagnostics_eq result
    have appended : input.diagnostics ++ topItemRecoveryDiagnostics trace =
        input.diagnostics ++ topItemRecoveryDiagnostics [] := by
      simpa only [topItemRecoveryDiagnostics, List.map_nil, List.append_nil]
        using traceEq.symm.trans unchanged
    exact topItemRecoveryDiagnostics_injective (List.append_cancel_left appended)

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TopItemUnrecognizedTraceProperties
/-! Independent absence of every top-item start selects an unchanged,
uncommitted rejection before file-level recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The independent absent-start condition includes hard keywords, contextual
declarations, and the leading derive hash. -/
theorem atTopItemStart_eq_false_of_topItemStartAbsent
    {input : State}
    (absent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
    atTopItemStart input = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true present with
    ⟨kind, member, span, token⟩
  exact absent kind member ⟨span, token⟩

/-- No recognized declaration or derive attribute is attempted when every
independent start token is absent. The rejection leaves diagnostics unchanged. -/
theorem parseItemsItem_eq_rejectAt_of_topItemStartAbsent
    {input : State}
    (absent : DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
    parseItemsItem input =
      rejectAt input { head := .topItem, tail := [] } .topItem := by
  have keywordAbsent (value : HardKeyword)
      (member : TokenKind.keyword value ∈
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
      isKeyword input value = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent (.keyword value) member
      (plainTopItemTokenPresentAt_of_isKeyword_eq_true value present)
  have contextualAbsent (value : ContextualKeyword)
      (member : TokenKind.identifier value.spelling ∈
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds) :
      isContextual input value = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact absent (.identifier value.spelling) member
      (plainTopItemTokenPresentAt_of_isContextual_eq_true value present)
  have hashAbsent : isSymbol input .hash = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    rcases symbol_eq_ok_of_isSymbol_eq_true .hash .topItem present with
      ⟨token, result⟩
    exact absent (.symbol .hash)
      (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds])
      ⟨token.span, (symbol_success_exactTokenParses .hash .topItem result).1⟩
  simp [parseItemsItem, topItem, plainTopItem, hashAbsent,
    keywordAbsent .importKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .exportKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .pragmaKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .typeKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .functionKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .defaultKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    keywordAbsent .contractKw (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .enum (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .trait (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds]),
    contextualAbsent .impl (by simp [DeclarativeGrammar.ImportTerminatorTopItemStartKinds])]

end Solcore.Syntax.Parser.FileInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileSingleRecoveryTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DiagnosticCascadeProperties
/-! Exact correspondence between independent cascade filtering and the public
normalization of top-item recovery event lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open FileInternals

/-- Independent keep/drop decisions determine the complete filtered event list. -/
theorem filterParseDiagnostics_recoveredTopItems_of_filters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept : List SourceSpan}
    (filtered : DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept := by
  induction filtered with
  | nil => simp [topItemRecoveryDiagnostics]
  | keep retained tail ih =>
      simp only [topItemRecoveryDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_recovered_of_retained _ _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      simp only [topItemRecoveryDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_recovered_of_suppressed _ _ _ _ _ suppressed, ih]

/-- Recovery-event normalization and the independent span-filter relation
agree in both directions, including order and duplicates. -/
theorem filterParseDiagnostics_recoveredTopItems_iff
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan) :
    DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept ↔
      filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
        topItemRecoveryDiagnostics kept := by
  constructor
  · exact filterParseDiagnostics_recoveredTopItems_of_filters file lexical
  · intro result
    rcases DeclarativeGrammar.lexicalCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have equal := topItemRecoveryDiagnostics_injective
      ((filterParseDiagnostics_recoveredTopItems_of_filters file lexical filtered).symm.trans
        result)
    simpa only [equal] using filtered

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaPrefixBoundaryTraceProperties
/-! Exact raw file results for successful pragma prefixes ending in rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Each successful prefix declaration costs one loop step; the final step
rewinds the rejected pragma and commits its report after all preceding events. -/
theorem parseItems_pragmaPrefixBoundary_trace_of_length_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      input.file.id input.window.endByte input.declarativeRemainder
      declarations stopped diagnostic trace)
    (adequate : declarations.length < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) := by
  induction fuel generalizing itemsRev input declarations stopped diagnostic trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | stopped marker recognized rejected =>
          rcases (pragmaDecl_trace_reject_iff (input := input)).mp rejected with
            ⟨failure, failed, declarationResult, _, reportEq, declarationTrace⟩
          have itemResult : parseItemsItem input = .reject failure failed := by
            unfold parseItemsItem
            rw [topItem_eq_pragma_of_exactTokenParses recognized]
            simp only [mapTopItem, declarationResult]
          rcases parseItems_boundaryStop_trace_exact fuel itemsRev recognized.1.1
              (atTopItemStart_eq_true_of_pragmaToken recognized) itemResult with
            ⟨output, result, outputRemainder, outputTrace⟩
          have frame := pragmaDecl_preservesTokenWindow input
          rw [declarationResult] at frame
          have rewind : { failed.declarativeRemainder with cursor := input.cursor } =
              input.declarativeRemainder := by
            simp only [State.declarativeRemainder, frame.1, frame.2]
          refine ⟨output, ?_, outputRemainder.trans rewind, ?_⟩
          · simpa only [List.map_nil, List.append_nil] using result
          · rw [outputTrace, declarationTrace, reportEq, List.append_assoc]
      | cons headParsed tailParsed =>
          rename_i afterHead head tail headTrace tailTrace
          rcases (pragmaDecl_trace_success_iff (input := input)).mp headParsed with
            ⟨next, declarationResult, nextRemainder, nextTrace⟩
          have marker : ∃ span afterKeyword,
              DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
                input.declarativeRemainder span afterKeyword := by
            cases headParsed.1 with
            | parsed span _ keywordParsed _ _ _ => exact ⟨span, _, keywordParsed⟩
          rcases marker with ⟨span, afterKeyword, keywordParsed⟩
          have itemResult : parseItemsItem input = .ok (wrapPragma head) next := by
            unfold parseItemsItem
            rw [topItem_eq_pragma_of_exactTokenParses keywordParsed]
            simp only [mapTopItem, declarationResult]
          have progress := pragmaDecl_cursor_lt_onSuccess declarationResult
          have notEnded : input.atEnd = false :=
            decide_eq_false (Nat.not_le_of_gt headParsed.1.startsInside)
          have context := pragmaDecl_success_context_eq declarationResult
          have tailAtNext : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
              next.file.id next.window.endByte next.declarativeRemainder
              tail stopped diagnostic tailTrace := by
            simpa only [context.1, context.2, nextRemainder] using tailParsed
          rcases ih (wrapPragma head :: itemsRev) tailAtNext (by
              simp only [List.length_cons] at adequate; omega) with
            ⟨output, result, remainderEq, traceEq⟩
          refine ⟨output, ?_, remainderEq, ?_⟩
          · simp only [parseItems, notEnded, Bool.false_eq_true, if_false,
              itemResult, progress, if_true]
            simpa only [List.reverse_cons, List.append_assoc,
              List.singleton_append, List.map_cons] using result
          · rw [traceEq, nextTrace]
            simp only [List.append_assoc]

/-- A remaining-token bound suffices independently of declaration sizes and
prior accumulated items, without requiring a valid initial state. -/
theorem parseItems_pragmaPrefixBoundary_trace_of_remainingCount_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      input.file.id input.window.endByte input.declarativeRemainder
      declarations stopped diagnostic trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) := by
  apply parseItems_pragmaPrefixBoundary_trace_of_length_lt fuel itemsRev parsed
  have bound : declarations.length < input.remainingCount := parsed.length_lt_remaining
  omega

/-- Production fuel is sufficient for every independent recognized-stop
prefix. Existing reverse-prefix items are returned without re-emitting events. -/
theorem parseItems_production_pragmaPrefixBoundary_trace
    (itemsRev : List TopItem) {input : State} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      input.file.id input.window.endByte input.declarativeRemainder
      declarations stopped diagnostic trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) :=
  parseItems_pragmaPrefixBoundary_trace_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev parsed (by omega)

/-- File wrapping attaches comments to successful declarations only. The
rejected pragma contributes its final report, no AST, and its rewound start. -/
theorem sourceFile_pragmaPrefixBoundary_trace (comments : List Comment)
    {input : State} {declarations : List PragmaDecl}
    {stopped : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaPrefixBoundaryTraceParses
      input.file.id input.window.endByte input.declarativeRemainder
      declarations stopped diagnostic trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := (declarations.map wrapPragma).map (attachTopItemComments input.file comments)
        comments
      } output ∧
      output.declarativeRemainder = stopped ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) := by
  rcases parseItems_production_pragmaPrefixBoundary_trace [] parsed with
    ⟨output, result, remainderEq, traceEq⟩
  refine ⟨output, ?_, remainderEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, List.nil_append, result]

end Solcore.Syntax.Parser.FileInternals
end
