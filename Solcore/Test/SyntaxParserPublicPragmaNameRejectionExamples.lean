import Solcore.Syntax.Parser.PublicPragmaNameRejectionOutputProperties

/-! Ground pragma-name failures determine complete public outputs through
independent grammar. Only lexical fixtures are reduced by the kernel. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals
open Solcore.Syntax.DeclarativeGrammar

def exampleSource : SourceId := { origin := .main, path := "pragma-name-examples.sol" }

def exampleFile (content : String) : SourceFile := { id := exampleSource, content }

def byteSpan (startByte endByte : Nat) : SourceSpan := {
  source := exampleSource, startByte, endByte
}

def pragmaToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 6), value := .keyword .pragmaKw
}

def semicolonToken (offset : Nat) : Token := {
  span := byteSpan offset (offset + 1), value := .symbol .semicolon
}

def pragmaTokens (offset : Nat) (rest : List Token) : List Token :=
  pragmaToken offset :: semicolonToken (offset + 7) :: rest

def lexicalCarrier (tokens : List Token) (diagnostics : List LexicalDiagnostic) : LexedFile := {
  source := exampleSource, tokens, comments := [], diagnostics
}

def expectedOutput (content : String) (tokens : List Token)
    (lexical : List LexicalDiagnostic) (parsed : List ParseDiagnostic) : ParseOutput := {
  parsed := {
    source := exampleSource
    span := SourceSpan.fullFile (exampleFile content)
    items := []
    comments := []
  }
  tokens
  lexicalDiagnostics := lexical
  parseDiagnostics := parsed
}

/-- An actual lexical fixture supplies exactly the carrier used by the grammar. -/
theorem lex_ok_of_toOption {file : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex file).toOption = some lexed) : Lexer.lex file = .ok lexed := by
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

/-- The semicolon is an independently observed non-name after the marker. -/
theorem pragmaSemicolonMissing (content : String) (offset : Nat) (rest : List Token) :
    PragmaNameMissingAt (exampleFile content).id (exampleFile content).content.utf8ByteSize
      (sourceFileRootRemainder (pragmaTokens offset rest))
      { sourceFileRootRemainder (pragmaTokens offset rest) with cursor := 1 }
      (byteSpan (offset + 7) (offset + 7 + 1)) (some (.symbol .semicolon)) := by
  apply PragmaNameMissingAt.missing (marker := (pragmaToken offset).span)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, pragmaTokens, pragmaToken]
  · simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder, pragmaTokens, semicolonToken]
  · apply CurrentInputAt.token (current := semicolonToken (offset + 7))
    simp [TokenAt, sourceFileRootRemainder, pragmaTokens]

/-- The marker preserves nesting and the semicolon resets it before the tail. -/
theorem pragmaTokensClear (offset : Nat) (rest : List Token) (clears : NestingClears rest) :
    NestingClears (pragmaTokens offset rest) :=
  .preserve rfl (.reset rfl clears)

/-- Grammar, canonical lexical validation, and independent filtering compute
both public entry points, including all lexical and diagnostic fields. -/
theorem completeOutputs {content : String} {tokens : List Token}
    {lexical : List LexicalDiagnostic} {after : Remainder}
    {span : SourceSpan} {found : Option TokenKind} {kept : List SourceSpan}
    (lexing : Lexer.lex (exampleFile content) = .ok (lexicalCarrier tokens lexical))
    (clears : NestingClears tokens)
    (missing : PragmaNameMissingAt (exampleFile content).id
      (exampleFile content).content.utf8ByteSize (sourceFileRootRemainder tokens)
      after span found)
    (filtered : LexicalCascadeFilters content (lexical.map (·.span)) [span] kept) :
    parseLexed (exampleFile content) (lexicalCarrier tokens lexical) =
        .ok (expectedOutput content tokens lexical
          (unexpectedDiagnostics found { head := .identifier, tail := [] } .pragmaDecl kept)) ∧
      parse (exampleFile content) = .ok (expectedOutput content tokens lexical
        (unexpectedDiagnostics found { head := .identifier, tail := [] } .pragmaDecl kept)) := by
  have accepted : LexedFileValidationAccepts (exampleFile content)
      (lexicalCarrier tokens lexical) :=
    (lexedFileValidationAccepts_iff_validFor _ _).mpr (Lexer.lex_ok_validFor _ _ lexing)
  exact ⟨parseLexed_eq_ok_of_pragmaNameMissing accepted clears missing filtered,
    parse_eq_ok_of_pragmaNameMissing lexing clears missing filtered⟩

set_option maxRecDepth 4096 in
private theorem eofLexes :
    Lexer.lex (exampleFile "pragma") = .ok (lexicalCarrier [pragmaToken 0] []) := by
  apply lex_ok_of_toOption
  decide +kernel

private theorem eofMissing :
    PragmaNameMissingAt exampleSource 6 (sourceFileRootRemainder [pragmaToken 0])
      { sourceFileRootRemainder [pragmaToken 0] with cursor := 1 } (byteSpan 6 6) none := by
  apply PragmaNameMissingAt.missing (marker := byteSpan 0 6)
  · simp [ExactTokenParses, TokenAt, sourceFileRootRemainder, pragmaToken]
  · simp [IdentifierAbsentAt, TokenAt, sourceFileRootRemainder]
  · exact .windowEnd (by decide)

/-- EOF reports no found token at the exact zero-width byte-6 endpoint. -/
theorem eof_parse_eq_output :
    parse (exampleFile "pragma") = .ok (expectedOutput "pragma" [pragmaToken 0] []
      [{
        span := byteSpan 6 6
        kind := .unexpected none { head := .identifier, tail := [] } .pragmaDecl
      }]) :=
  (completeOutputs eofLexes (.preserve rfl .done) eofMissing
    (lexicalCascadeFilters_nil_lexical "pragma" [byteSpan 6 6])).2

set_option maxRecDepth 4096 in
private theorem semicolonLexes :
    Lexer.lex (exampleFile "pragma ;") = .ok (lexicalCarrier (pragmaTokens 0 []) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The failure records the actual semicolon at bytes 7..8, not the marker. -/
theorem semicolon_parse_eq_output :
    parse (exampleFile "pragma ;") = .ok (expectedOutput "pragma ;" (pragmaTokens 0 []) []
      [{
        span := byteSpan 7 8
        kind := .unexpected (some (.symbol .semicolon))
          { head := .identifier, tail := [] } .pragmaDecl
      }]) :=
  (completeOutputs semicolonLexes (pragmaTokensClear 0 [] .done)
    (pragmaSemicolonMissing "pragma ;" 0 [])
    (lexicalCascadeFilters_nil_lexical "pragma ;" [byteSpan 7 8])).2

private def laterTokens : List Token := [
  { span := byteSpan 9 13, value := .keyword .typeKw },
  { span := byteSpan 14 19, value := .identifier "Later" },
  { span := byteSpan 20 21, value := .symbol .equal },
  { span := byteSpan 22 26, value := .identifier "word" },
  semicolonToken 26
]

set_option maxRecDepth 4096 in
private theorem laterLexes :
    Lexer.lex (exampleFile "pragma ; type Later = word;") =
      .ok (lexicalCarrier (pragmaTokens 0 laterTokens) []) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Even a valid following declaration is retained only as tokens: recognized
start rejection commits one report and returns an empty item list. -/
theorem laterTokens_parse_eq_output :
    parse (exampleFile "pragma ; type Later = word;") =
      .ok (expectedOutput "pragma ; type Later = word;" (pragmaTokens 0 laterTokens) []
        [{
          span := byteSpan 7 8
          kind := .unexpected (some (.symbol .semicolon))
            { head := .identifier, tail := [] } .pragmaDecl
        }]) :=
  (completeOutputs laterLexes
    (pragmaTokensClear 0 laterTokens
      (.preserve rfl (.preserve rfl (.preserve rfl (.preserve rfl (.reset rfl .done))))))
    (pragmaSemicolonMissing "pragma ; type Later = word;" 0 laterTokens)
    (lexicalCascadeFilters_nil_lexical "pragma ; type Later = word;" [byteSpan 7 8])).2

/-- The internal root remainder is rewound unchanged, proving that the later
tokens really remain unconsumed; this endpoint is hidden by public ParseOutput. -/
theorem laterTokens_sourceFile_remainsAtRoot :
    ∃ output, sourceFile [] (State.initial (exampleFile "pragma ; type Later = word;")
        (lexicalCarrier (pragmaTokens 0 laterTokens) [])) = .ok {
          source := exampleSource
          span := SourceSpan.fullFile (exampleFile "pragma ; type Later = word;")
          items := []
          comments := []
        } output ∧
      output.declarativeRemainder = sourceFileRootRemainder (pragmaTokens 0 laterTokens) := by
  have missing := pragmaSemicolonMissing "pragma ; type Later = word;" 0 laterTokens
  cases missing with
  | missing keywordParsed absent current =>
      rcases parseItemsItem_pragmaNameMissing_exact
          (input := State.initial (exampleFile "pragma ; type Later = word;")
            (lexicalCarrier (pragmaTokens 0 laterTokens) []))
          keywordParsed absent current with ⟨rejected, _after, _prior⟩
      rcases sourceFile_boundaryStop_trace_exact [] keywordParsed.1.1
          (atTopItemStart_eq_true_of_pragmaToken
            (input := State.initial (exampleFile "pragma ; type Later = word;")
              (lexicalCarrier (pragmaTokens 0 laterTokens) [])) keywordParsed) rejected with
        ⟨output, result, remainderEq, _trace⟩
      exact ⟨output, result, remainderEq⟩

end Solcore.Test.SyntaxParserPublicPragmaNameRejectionExamples
