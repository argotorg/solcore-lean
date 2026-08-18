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
Public parsing succeeds exactly when the supplied token stream is the lexer
output and the requested tree satisfies the declarative grammar.
-/
theorem parseLexed_eq_ok_iff
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile) :
    parseLexed file lexed = .ok parsed ↔
      Lexer.lex file = .ok lexed ∧
        FileParses lexed parsed := by
  constructor
  · intro success
    have provenance :=
      parseLexed_success_provenance file lexed parsed success
    exact ⟨
      provenance.1,
      parseLexed_success_fileParses file lexed parsed success
    ⟩
  · rintro ⟨lexing, derivation⟩
    have conformance := FileParses.conformsTo_of_lexes file derivation
      (Lexer.lex_success_lexes file lexed lexing)
    exact parseLexed_complete
      file lexed parsed lexing conformance derivation

/-- The parser accepts the exact lexer result past its canonical-input guard. -/
theorem parseLexed_ne_invalid_input_of_lexing
    (file : SourceFile)
    (lexed invalid : Lexed)
    (lexing : Lexer.lex file = .ok lexed) :
    parseLexed file lexed ≠
      .error (.internal (.invalidInput invalid)) := by
  intro failure
  exact (parseLexed_invalid_input_provenance
    file lexed invalid failure) lexing

/--
The parser's output-validation branch is unreachable: reaching it already
proves that the supplied stream is the exact lexer result, and the
executor-produced derivation entails the conformance it checks.
-/
theorem parseLexed_ne_invalid_output
    (file : SourceFile)
    (lexed : Lexed)
    (invalid : ParsedFile) :
    parseLexed file lexed ≠
      .error (.internal (.invalidOutput invalid)) := by
  intro failure
  obtain ⟨lexing, derivation, notConforming⟩ :=
    parseLexed_invalid_output_provenance file lexed invalid failure
  have lexical := Lexer.lex_success_lexes file lexed lexing
  have conformance :=
    FileParses.conformsTo_of_lexes file derivation lexical
  exact notConforming conformance

/-- Public frontend parsing cannot report a parser input invariant. -/
theorem parse_ne_parser_invalid_input
    (file : SourceFile)
    (invalid : Lexed) :
    parse file ≠
      .error (.internal (.parser (.invalidInput invalid))) := by
  intro failure
  obtain ⟨lexed, lexing, parsing⟩ :=
    parse_parser_invariant_provenance
      file (.invalidInput invalid) failure
  exact parseLexed_ne_invalid_input_of_lexing
    file lexed invalid lexing parsing

/-- Public frontend parsing cannot report a parser output invariant. -/
theorem parse_ne_parser_invalid_output
    (file : SourceFile)
    (invalid : ParsedFile) :
    parse file ≠
      .error (.internal (.parser (.invalidOutput invalid))) := by
  intro failure
  obtain ⟨lexed, lexing, parsing⟩ :=
    parse_parser_invariant_provenance
      file (.invalidOutput invalid) failure
  exact parseLexed_ne_invalid_output file lexed invalid parsing

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

/--
Frontend parsing succeeds exactly when some lexer output carries a complete
declarative parse derivation for the requested tree.
-/
theorem parse_eq_ok_iff
    (file : SourceFile)
    (parsed : ParsedFile) :
    parse file = .ok parsed ↔
      ∃ lexed,
        Lexer.lex file = .ok lexed ∧
          FileParses lexed parsed := by
  constructor
  · intro success
    obtain ⟨lexed, lexing, _, _, _, derivation⟩ :=
      parse_success_provenance file parsed success
    exact ⟨lexed, lexing, derivation⟩
  · rintro ⟨lexed, lexing, derivation⟩
    have conformance := FileParses.conformsTo_of_lexes file derivation
      (Lexer.lex_success_lexes file lexed lexing)
    exact parse_complete
      file lexed parsed lexing conformance derivation

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
