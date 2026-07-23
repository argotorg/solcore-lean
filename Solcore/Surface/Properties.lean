import Solcore.Surface.Parser
import Solcore.Surface.GrammarProperties

set_option autoImplicit false

namespace Solcore.Surface

namespace Lexer

theorem lex_success_tokens_exact
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    ∀ token ∈ lexed.tokens, token.ValidFor file :=
  (lex_success_valid file lexed success).1

theorem lex_success_comments_exact
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    ∀ comment ∈ lexed.comments, comment.ValidFor file :=
  (lex_success_valid file lexed success).2.1

theorem lex_success_tokens_maximal
    (file : SourceFile)
    (lexed : Lexed)
    (success : lex file = .ok lexed) :
    ∀ token ∈ lexed.tokens,
      LexicalGrammar.TokenMaximalFor token file :=
  (lex_success_lexes file lexed success).2

end Lexer

namespace Parser

/--
Any successful executor result is the unique result allowed by an existing
complete-file grammar derivation for the same token stream.
-/
theorem parseLexed_success_matches_derivation
    (file : SourceFile)
    (lexed : Lexed)
    (expected parsed : ParsedFile)
    (derivation : FileParses lexed expected)
    (success : parseLexed file lexed = .ok parsed) :
    parsed = expected :=
  FileParses.deterministic
    (parseLexed_success_fileParses file lexed parsed success)
    derivation

theorem parse_success_provenance
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok parsed ∧
      LexicalGrammar.Lexes file lexed ∧
      parsed.ConformsTo file lexed ∧
      FileParses lexed parsed := by
  cases lexing : Lexer.lex file with
  | error failure =>
      cases failure with
      | source error =>
          simp [parse, lexing] at success
      | internal invariant =>
          simp [parse, lexing] at success
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error failure =>
          cases failure with
          | source error =>
              simp [parse, lexing, parsing] at success
          | internal invariant =>
              simp [parse, lexing, parsing] at success
      | ok parsedResult =>
          simp [parse, lexing, parsing] at success
          cases success
          refine ⟨lexed, rfl, parsing, ?_, ?_, ?_⟩
          · exact Lexer.lex_success_lexes file lexed lexing
          · exact (parseLexed_success_conforms
              file lexed parsed parsing).2
          · exact parseLexed_success_fileParses
              file lexed parsed parsing

theorem parse_success_has_valid_lexing
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed, Lexer.lex file = .ok lexed ∧ lexed.ValidFor file := by
  obtain ⟨lexed, lexing, _, lexical, _, _⟩ :=
    parse_success_provenance file parsed success
  exact ⟨lexed, lexing, lexical.1⟩

theorem parse_success_grammar_valid
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    parsed.GrammarValid := by
  obtain ⟨_, _, _, _, conformance, _⟩ :=
    parse_success_provenance file parsed success
  exact conformance.2.2

theorem parse_success_consumes_all_tokens
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok parsed ∧
      parsed.CorrespondsTo lexed := by
  obtain ⟨lexed, lexing, parsing, _, conformance, _⟩ :=
    parse_success_provenance file parsed success
  exact ⟨lexed, lexing, parsing, conformance.2.1⟩

theorem parse_success_spans_valid
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    parsed.ValidFor file :=
  parse_success_valid file parsed success

end Parser

end Solcore.Surface
