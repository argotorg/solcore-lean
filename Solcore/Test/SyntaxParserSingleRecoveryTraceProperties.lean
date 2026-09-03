import Solcore.Syntax.Parser.SourceFileSingleRecoveryTraceProperties

/-! Compile-time consumers of grammar-derived single-recovery file traces. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSingleRecoveryTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

example := @atTopItemStart_eq_false_of_topItemStartAbsent
example := @parseItemsItem_eq_rejectAt_of_topItemStartAbsent
example := @recoveredTopItem_eq_error
example := @parseItems_singleRecoveryToEnd_exact
example := @parseItems_production_singleRecoveryToEnd_exact
example := @sourceFile_singleRecoveryToEnd_exact

example (comments : List Comment)
    {input : State} {item : TopItem} {after : Remainder}
    (startsAbsent : TopItemKindsAbsentAt input.declarativeRemainder
      ImportTerminatorTopItemStartKinds)
    (recovered : TopItemRecoveryParses input.declarativeRemainder item after)
    (atEnd : after.cursor = input.window.endIndex) :
    ∃ output, sourceFile comments input = .ok {
        source := input.file.id
        span := SourceSpan.fullFile input.file
        items := [attachTopItemComments input.file comments item]
        comments
      } output ∧
      output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++
        [{ span := item.span, kind := .recovered .topItem }] :=
  sourceFile_singleRecoveryToEnd_exact comments startsAbsent recovered atEnd

private def exampleFile : SourceFile := {
  id := { origin := .main, path := "single-recovery.sol" }
  content := ";"
}

private def exampleSpan : SourceSpan := SourceSpan.fullFile exampleFile

private def exampleInput (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile
  tokens := #[{ span := exampleSpan, value := .symbol .semicolon }]
  cursor := 0
  window := { endIndex := 1, endByte := 1 }
  diagnosticsRev := priorRev
}

private theorem exampleStartsAbsent (priorRev : List ParseDiagnostic) :
    TopItemKindsAbsentAt (exampleInput priorRev).declarativeRemainder
      ImportTerminatorTopItemStartKinds := by
  simp [TopItemKindsAbsentAt, ImportTerminatorTopItemStartKinds, TokenKindAbsentAt,
    State.declarativeRemainder, exampleInput, TokenAt]

private theorem exampleRecovers (priorRev : List ParseDiagnostic) :
    TopItemRecoveryParses (exampleInput priorRev).declarativeRemainder
      (recoveredTopItemValue exampleSpan exampleSpan)
      { (exampleInput priorRev).declarativeRemainder with cursor := 1 } := by
  apply TopItemRecoveryParses.recovered
    (token := { span := exampleSpan, value := .symbol .semicolon })
  · simp [TokenAt, State.declarativeRemainder, exampleInput]
  · exact .stop (.windowEnd (by simp [State.declarativeRemainder, exampleInput]))

/-- A real non-start token derives the exact result without an execution
hypothesis, including arbitrary retained diagnostics and supplied comments. -/
example (priorRev : List ParseDiagnostic) (comments : List Comment) :
    ∃ output, sourceFile comments (exampleInput priorRev) = .ok {
        source := exampleFile.id
        span := SourceSpan.fullFile exampleFile
        items := [attachTopItemComments exampleFile comments
          (recoveredTopItemValue exampleSpan exampleSpan)]
        comments
      } output ∧
      output.cursor = 1 ∧
      output.diagnostics = priorRev.reverse ++
        [{ span := exampleSpan, kind := .recovered .topItem }] := by
  rcases sourceFile_singleRecoveryToEnd_exact comments (exampleStartsAbsent priorRev)
      (exampleRecovers priorRev) rfl with ⟨output, result, after, trace⟩
  refine ⟨output, result, congrArg Remainder.cursor after, ?_⟩
  simpa [exampleInput, State.diagnostics, recoveredTopItemValue, SourceSpan.cover]
    using trace

end Solcore.Test.SyntaxParserSingleRecoveryTraceProperties
