import Solcore.Surface.Parser

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

end Lexer

namespace Parser

theorem parse_success_provenance
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
      parseLexed file lexed = .ok parsed ∧
      lexed.ValidFor file ∧
      parsed.ConformsTo file lexed := by
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
          refine ⟨lexed, rfl, parsing, ?_, ?_⟩
          · exact Lexer.lex_success_valid file lexed lexing
          · exact (parseLexed_success_conforms
              file lexed parsed parsing).2

theorem parse_success_has_valid_lexing
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed, Lexer.lex file = .ok lexed ∧ lexed.ValidFor file := by
  obtain ⟨lexed, lexing, _, valid, _⟩ :=
    parse_success_provenance file parsed success
  exact ⟨lexed, lexing, valid⟩

theorem parse_success_grammar_valid
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    parsed.GrammarValid := by
  obtain ⟨_, _, _, _, conformance⟩ :=
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
  obtain ⟨lexed, lexing, parsing, _, conformance⟩ :=
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
