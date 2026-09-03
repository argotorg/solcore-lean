import Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties

/-! Ground public-output examples derived through independent single-token
recovery, nesting, validation, and lexical-cascade grammar. Parser results are
proved using the public correspondence theorems, not by evaluating the parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicSingleRecoveryExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

private def exampleSource : SourceId := {
  origin := .main
  path := "single-recovery-examples.sol"
}

private def exampleFile (content : String) : SourceFile := {
  id := exampleSource
  content
}

private def byteSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleSource
  startByte
  endByte
}

private def semicolon (offset : Nat) : Token := {
  span := byteSpan offset (offset + 1)
  value := .symbol .semicolon
}

private def lexicalCarrier (offset : Nat)
    (diagnostics : List LexicalDiagnostic) : LexedFile := {
  source := exampleSource
  tokens := [semicolon offset]
  comments := []
  diagnostics
}

private def errorItem (offset : Nat) : TopItem := {
  span := byteSpan offset (offset + 1)
  leadingComments := []
  value := .error
}

private def expectedOutput (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) (parsed : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := [errorItem offset]
    comments := []
  }
  tokens := [semicolon offset]
  lexicalDiagnostics := lexical
  parseDiagnostics := parsed
}

private theorem semicolonStartsAbsent (offset : Nat)
    (lexical : List LexicalDiagnostic) :
    TopItemKindsAbsentAt
      (sourceFileRootRemainder (lexicalCarrier offset lexical).tokens)
      ImportTerminatorTopItemStartKinds := by
  simp [TopItemKindsAbsentAt, ImportTerminatorTopItemStartKinds,
    TokenKindAbsentAt, sourceFileRootRemainder, lexicalCarrier, semicolon, TokenAt]

private theorem semicolonRecovers (offset : Nat)
    (lexical : List LexicalDiagnostic) :
    TopItemRecoveryParses
      (sourceFileRootRemainder (lexicalCarrier offset lexical).tokens)
      (errorItem offset)
      { sourceFileRootRemainder (lexicalCarrier offset lexical).tokens with cursor := 1 } := by
  apply TopItemRecoveryParses.recovered (token := semicolon offset)
  · simp [TokenAt, sourceFileRootRemainder, lexicalCarrier]
  · exact .stop (.windowEnd (by simp [sourceFileRootRemainder, lexicalCarrier]))

private theorem semicolonNestingClears (offset : Nat)
    (lexical : List LexicalDiagnostic) :
    NestingClears (lexicalCarrier offset lexical).tokens :=
  .reset rfl .done

private theorem completeOutputs (content : String) (offset : Nat)
    (lexical : List LexicalDiagnostic) (kept : List SourceSpan)
    (lexing : Lexer.lex (exampleFile content) = .ok (lexicalCarrier offset lexical))
    (filtered : LexicalCascadeFilters content (lexical.map (·.span))
      [(errorItem offset).span] kept) :
    parseLexed (exampleFile content) (lexicalCarrier offset lexical) =
        .ok (expectedOutput content offset lexical (topItemRecoveryDiagnostics kept)) ∧
      parse (exampleFile content) =
        .ok (expectedOutput content offset lexical (topItemRecoveryDiagnostics kept)) := by
  have accepted : LexedFileValidationAccepts (exampleFile content)
      (lexicalCarrier offset lexical) :=
    (lexedFileValidationAccepts_iff_validFor _ _).mpr
      (Lexer.lex_ok_validFor _ _ lexing)
  have tokenized := parseLexed_eq_ok_of_singleRecoveryToEnd accepted
    (semicolonNestingClears offset lexical) (semicolonStartsAbsent offset lexical)
    (semicolonRecovers offset lexical) rfl filtered
  have sourced := parse_eq_ok_of_singleRecoveryToEnd lexing
    (semicolonNestingClears offset lexical) (semicolonStartsAbsent offset lexical)
    (semicolonRecovers offset lexical) rfl filtered
  exact ⟨tokenized, sourced⟩

private def invalidToken : LexicalDiagnostic := {
  span := byteSpan 0 2
  kind := .invalidToken
}

private theorem lex_ok_of_toOption {file : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex file).toOption = some lexed) :
    Lexer.lex file = .ok lexed := by
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual =>
      simp only [result, Except.toOption] at checked
      cases checked
      rfl

set_option maxRecDepth 4096 in
private theorem semicolonLexes :
    Lexer.lex (exampleFile ";") = .ok (lexicalCarrier 0 []) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 4096 in
private theorem sameLineLexes :
    Lexer.lex (exampleFile "§ ;") = .ok (lexicalCarrier 3 [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 4096 in
private theorem nextLineLexes :
    Lexer.lex (exampleFile "§\n;") = .ok (lexicalCarrier 3 [invalidToken]) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- A bare semicolon is one error AST with exactly one top-item recovery event. -/
theorem semicolon_parse_eq_output :
    parse (exampleFile ";") = .ok (expectedOutput ";" 0 []
      [{ span := byteSpan 0 1, kind := .recovered .topItem }]) :=
  (completeOutputs ";" 0 [] [byteSpan 0 1] semicolonLexes
    (lexicalCascadeFilters_nil_lexical ";" [byteSpan 0 1])).2

private theorem sameLineSuppressed :
    LexicalCascadeSuppresses "§ ;" [invalidToken.span] (byteSpan 3 4) := by
  refine ⟨invalidToken.span, by simp, rfl, Or.inl ?_⟩
  decide

/-- The invalid character's two UTF-8 bytes remain a lexical diagnostic, while
same-line cascade suppression removes only the semicolon's recovery event. -/
theorem sameLine_parse_eq_output :
    parse (exampleFile "§ ;") =
      .ok (expectedOutput "§ ;" 3 [invalidToken] []) :=
  (completeOutputs "§ ;" 3 [invalidToken] [] sameLineLexes
    (.drop sameLineSuppressed .nil)).2

private theorem nextLineRetained :
    ¬ LexicalCascadeSuppresses "§\n;" [invalidToken.span] (byteSpan 3 4) := by
  rintro ⟨span, member, _sourceEq, suppressed⟩
  have spanEq : span = invalidToken.span := by simpa using member
  subst span
  rcases suppressed with sameLine | overlap | covered | adjacent
  · exact (by decide : cascadeLineIndex "§\n;" invalidToken.span.startByte ≠
      cascadeLineIndex "§\n;" (byteSpan 3 4).startByte) sameLine
  · exact (by decide : ¬ (byteSpan 3 4).startByte < invalidToken.span.endByte) overlap.2
  · exact (by decide : ¬ (byteSpan 3 4).startByte ≤ invalidToken.span.endByte) covered.2
  · rcases adjacent with ⟨_ordered, gap, sliced, whitespace⟩
    have exactGap : Trivia.utf8Slice? "§\n;" invalidToken.span.endByte
        (byteSpan 3 4).startByte = some "\n" := by decide
    have gapEq : gap = "\n" := Option.some.inj (sliced.symm.trans exactGap)
    subst gap
    contradiction

/-- LF separates the lexical error from the recovery event, so both distinct
diagnostics survive at their exact UTF-8 byte ranges. -/
theorem nextLine_parse_eq_output :
    parse (exampleFile "§\n;") = .ok (expectedOutput "§\n;" 3 [invalidToken]
      [{ span := byteSpan 3 4, kind := .recovered .topItem }]) :=
  (completeOutputs "§\n;" 3 [invalidToken] [byteSpan 3 4] nextLineLexes
    (.keep nextLineRetained .nil)).2

/-- The already-tokenized public entry point exposes the same fully determined
output, using the independently certified canonical lexical carrier. -/
theorem sameLine_parseLexed_eq_output :
    parseLexed (exampleFile "§ ;") (lexicalCarrier 3 [invalidToken]) =
      .ok (expectedOutput "§ ;" 3 [invalidToken] []) :=
  (completeOutputs "§ ;" 3 [invalidToken] [] sameLineLexes
    (.drop sameLineSuppressed .nil)).1

end Solcore.Test.SyntaxParserPublicSingleRecoveryExamples
