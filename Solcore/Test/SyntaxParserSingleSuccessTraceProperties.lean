import Solcore.Syntax.Parser.SourceFileSingleSuccessTraceProperties

/-! Consumers of executable single-success composition. These deliberately
assume the item reply and do not present it as an independent grammar proof. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSingleSuccessTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example (fuel : Nat) (itemsRev : List TopItem)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (fuel + 2) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  parseItems_singleSuccessToEnd_exact fuel itemsRev parsed atEnd

example (itemsRev : List TopItem) {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ [item]) output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  parseItems_production_singleSuccessToEnd_exact itemsRev parsed atEnd

example (comments : List Comment) {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = next.diagnostics :=
  sourceFile_singleSuccessToEnd_exact comments parsed atEnd

example (comments : List Comment) (trace : List ParseDiagnostic)
    {input next : State} {item : TopItem}
    (parsed : parseItemsItem input = .ok item next)
    (atEnd : next.cursor = input.window.endIndex)
    (childTrace : next.diagnostics = input.diagnostics ++ trace) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = next.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  rcases sourceFile_singleSuccessToEnd_exact comments parsed atEnd with
    ⟨output, result, remainderEq, traceEq⟩
  exact ⟨output, result, remainderEq, traceEq.trans childTrace⟩

end Solcore.Test.SyntaxParserSingleSuccessTraceProperties
