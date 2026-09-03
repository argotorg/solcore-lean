import Solcore.Syntax.Parser.SourceFileBoundaryStopTraceProperties

/-! Compositional consumers retain failed-attempt diagnostics at a file stop. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBoundaryStopTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (fuel : Nat) (itemsRev : List TopItem)
    {input failed : State} {failure : Failure}
    (inside : input.cursor < input.window.endIndex)
    (starts : atTopItemStart input = true)
    (rejected : parseItemsItem input = .reject failure failed) :
    ∃ output, parseItems (fuel + 1) itemsRev input = .ok itemsRev.reverse output ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  rcases parseItems_boundaryStop_trace_exact fuel itemsRev inside starts rejected with
    ⟨output, result, _, trace⟩
  exact ⟨output, result, trace⟩

example (comments : List Comment)
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
      output.cursor = input.cursor ∧
      output.diagnostics = failed.diagnostics ++ [failure.toDiagnostic] := by
  rcases sourceFile_boundaryStop_trace_exact comments inside starts rejected with
    ⟨output, result, remainderEq, trace⟩
  exact ⟨output, result, congrArg (·.cursor) remainderEq, trace⟩

end Solcore.Test.SyntaxParserBoundaryStopTraceProperties
