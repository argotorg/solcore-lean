import Solcore.Syntax.DeclarativePragmaPrefixBoundaryTraceProperties
import Solcore.Syntax.Parser.PragmaDeclarationContextProperties
import Solcore.Syntax.Parser.PragmaDeclarationRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.PragmaKeywordExecutionProperties
import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties

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
