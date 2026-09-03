import Solcore.Syntax.DeclarativePragmaSequenceTraceProperties
import Solcore.Syntax.Parser.PragmaDeclarationTraceProperties
import Solcore.Syntax.Parser.PragmaKeywordExecutionProperties

/-! Independent successful pragma sequences determine complete raw file-loop
traces. Existing reverse prefixes are returned but never parsed or diagnosed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- A pragma-only sequence executes at any fuel larger than its declaration
count. Its exact suffix follows the existing prefix without rediagnosing it. -/
theorem parseItems_pragmaSequence_trace_of_length_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace)
    (adequate : declarations.length < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing itemsRev input declarations after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | done atEnd =>
          have ended : input.atEnd = true := by
            exact decide_eq_true atEnd
          refine ⟨input, ?_, rfl, by simp⟩
          simp only [parseItems, ended, if_true, List.map_nil, List.append_nil]
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
          have inside := headParsed.1.startsInside
          have notEnded : input.atEnd = false := by
            exact decide_eq_false (Nat.not_le_of_gt inside)
          rw [← nextRemainder] at tailParsed
          rcases ih (wrapPragma head :: itemsRev) tailParsed (by
              simp only [List.length_cons] at adequate; omega) with
            ⟨output, result, remainderEq, traceEq⟩
          refine ⟨output, ?_, remainderEq, ?_⟩
          · simp only [parseItems, notEnded, Bool.false_eq_true, if_false,
              itemResult, progress, if_true]
            simpa only [List.reverse_cons, List.append_assoc,
              List.singleton_append, List.map_cons] using result
          · rw [traceEq, nextTrace, List.append_assoc]

/-- Remaining-token adequacy is a sufficient, declaration-count-independent
bound. Neither valid input nor initially empty diagnostics is required. -/
theorem parseItems_pragmaSequence_trace_of_remainingCount_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  apply parseItems_pragmaSequence_trace_of_length_lt fuel itemsRev parsed
  have bound : declarations.length ≤ input.remainingCount := parsed.length_le_remaining
  omega

/-- The production fuel always suffices for an independently derived complete
pragma sequence, retaining the precise fresh ASTs, endpoint, and raw trace. -/
theorem parseItems_production_pragmaSequence_trace
    (itemsRev : List TopItem) {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  parseItems_pragmaSequence_trace_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev parsed (by omega)

/-- The complete pragma-only window produces the exact comment-attached file.
File wrapping emits no event and does not reorder declarations or diagnostics. -/
theorem sourceFile_pragmaSequence_trace (comments : List Comment)
    {input : State} {declarations : List PragmaDecl}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.PragmaSequenceTraceParses
      input.declarativeRemainder declarations after trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := (declarations.map wrapPragma).map (attachTopItemComments input.file comments)
        comments
      } output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases parseItems_production_pragmaSequence_trace [] parsed with
    ⟨output, result, remainderEq, traceEq⟩
  refine ⟨output, ?_, remainderEq, traceEq⟩
  simp only [sourceFile, List.reverse_nil, List.nil_append, result]

end Solcore.Syntax.Parser.FileInternals
