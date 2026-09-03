import Solcore.Syntax.Parser.PragmaSequenceTraceProperties
import Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

/-! Independent pragma-sequence consumers preserve old item prefixes, exact
fresh declaration/diagnostic order, carrier endpoints, and supplied comments. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaSequenceTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
open Solcore.Test.SyntaxParserPublicPragmaSuccessExamples

example := @PragmaDeclOrdinaryParses.startsInside
example := @PragmaDeclOrdinaryParses.carrier_progress
example := @PragmaDeclOrdinaryParses.toTopItem
example := @PragmaSequenceTraceParses.carrier_atEnd
example := @PragmaSequenceTraceParses.length_le_remaining
example := @PragmaSequenceTraceParses.toFileItems
example := @PragmaSequenceTraceParses.result_unique
example := @parseItems_pragmaSequence_trace_of_length_lt
example := @parseItems_pragmaSequence_trace_of_remainingCount_lt
example := @parseItems_production_pragmaSequence_trace
example := @sourceFile_pragmaSequence_trace

/-- Empty grammar requires the active end, not an empty token array, and
preserves all existing items and raw diagnostics without a validity premise. -/
theorem emptySequence_retains_prefix (itemsRev : List TopItem) (input : State)
    (atEnd : input.window.endIndex ≤ input.cursor) :
    ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok itemsRev.reverse output ∧
      output.declarativeRemainder = input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics := by
  simpa only [List.map_nil, List.append_nil] using
    parseItems_production_pragmaSequence_trace itemsRev
      (input := input) (PragmaSequenceTraceParses.done atEnd)

/-- An already reversed two-item prefix is restored once, before every fresh
pragma; only the independent fresh sequence contributes additional diagnostics. -/
theorem reversePrefix_order (first second : TopItem)
    {input : State} {declarations : List PragmaDecl} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : PragmaSequenceTraceParses input.declarativeRemainder declarations after trace) :
    ∃ output, parseItems (input.remainingCount + 1) [second, first] input =
        .ok ([first, second] ++ declarations.map wrapPragma) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] using parseItems_production_pragmaSequence_trace [second, first] parsed

private def pairTokens : List Token := [pragmaToken 0, identifierToken 7 8 "a",
  identifierToken 9 12 "x-y", semicolonToken 12, pragmaToken 14,
  identifierToken 21 22 "b", identifierToken 23 26 "z-w", semicolonToken 26]

private def firstDeclaration : PragmaDecl := {
  span := byteSpan 0 13
  value := {
    name := { span := byteSpan 7 8, value := "a" }
    items := [{ span := byteSpan 9 12, value := "x-y" }] }
}

private def secondDeclaration : PragmaDecl := {
  span := byteSpan 14 27
  value := {
    name := { span := byteSpan 21 22, value := "b" }
    items := [{ span := byteSpan 23 26, value := "z-w" }] }
}

private def firstDiagnostic : ParseDiagnostic := {
  span := byteSpan 9 12, kind := .invalidIdentifierHyphen "x-y"
}

private def secondDiagnostic : ParseDiagnostic := {
  span := byteSpan 23 26, kind := .invalidIdentifierHyphen "z-w"
}

private theorem firstParsed :
    PragmaDeclTraceParses (sourceFileRootRemainder pairTokens) firstDeclaration
      (atCursor pairTokens 4) [firstDiagnostic] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "x-y".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor pairTokens 1) (afterName := atCursor pairTokens 2)
    (afterItems := atCursor pairTokens 3) (byteSpan 0 6) (byteSpan 12 13)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor pairTokens 3)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]

private theorem secondParsed :
    PragmaDeclTraceParses (atCursor pairTokens 4) secondDeclaration
      (atCursor pairTokens 8) [secondDiagnostic] := by
  refine ⟨?_, .cons (.hyphen (by change '-' ∈ "z-w".toList; decide)) .nil⟩
  apply PragmaDeclOrdinaryParses.parsed
    (afterKeyword := atCursor pairTokens 5) (afterName := atCursor pairTokens 6)
    (afterItems := atCursor pairTokens 7) (byteSpan 14 20) (byteSpan 26 27)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, pragmaToken]
  · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
  · apply PragmaItemsOrdinaryParses.nonempty (afterFirst := atCursor pairTokens 7)
    · simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · simp [IdentifierParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, identifierToken]
    · apply PragmaItemsTailOrdinaryParses.done
      simp [TokenKindAbsentAt, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, atCursor, pairTokens, semicolonToken]

private theorem pairParsed : PragmaSequenceTraceParses (sourceFileRootRemainder pairTokens)
    [firstDeclaration, secondDeclaration] (atCursor pairTokens 8)
    [firstDiagnostic, secondDiagnostic] :=
  .cons firstParsed (.cons secondParsed (.done (by decide)))

private def pairInput (priorRev : List ParseDiagnostic) : State := {
  file := exampleFile "pragma a x-y; pragma b z-w;"
  tokens := pairTokens.toArray
  cursor := 0
  window := { endIndex := 8, endByte := 27 }
  diagnosticsRev := priorRev
}

/-- Three loop steps suffice for two declarations and the final end check.
An existing copy of a hyphenated pragma is returned but not diagnosed again. -/
theorem existingPragmaPrefix_notRediagnosed (priorRev : List ParseDiagnostic) :
    ∃ output, parseItems 3 [wrapPragma firstDeclaration] (pairInput priorRev) =
        .ok [wrapPragma firstDeclaration, wrapPragma firstDeclaration,
          wrapPragma secondDeclaration] output ∧
      output.declarativeRemainder = atCursor pairTokens 8 ∧
      output.diagnostics = priorRev.reverse ++ [firstDiagnostic, secondDiagnostic] := by
  exact parseItems_pragmaSequence_trace_of_length_lt 3 [wrapPragma firstDeclaration]
    (input := pairInput priorRev) pairParsed (by decide)

/-- The production bound yields the same fresh order and raw trace, with all
supplied comments attached only by the source-file wrapper. -/
theorem pair_sourceFile_exact (priorRev : List ParseDiagnostic) (comments : List Comment) :
    ∃ output, sourceFile comments (pairInput priorRev) = .ok {
        source := exampleSource
        span := SourceSpan.fullFile (exampleFile "pragma a x-y; pragma b z-w;")
        items := [attachTopItemComments (pairInput priorRev).file comments
          (wrapPragma firstDeclaration), attachTopItemComments (pairInput priorRev).file comments
          (wrapPragma secondDeclaration)]
        comments
      } output ∧
      output.declarativeRemainder = atCursor pairTokens 8 ∧
      output.diagnostics = priorRev.reverse ++ [firstDiagnostic, secondDiagnostic] :=
  sourceFile_pragmaSequence_trace comments (input := pairInput priorRev) pairParsed

end Solcore.Test.SyntaxParserPragmaSequenceTraceProperties
