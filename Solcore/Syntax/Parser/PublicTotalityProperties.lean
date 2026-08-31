import Solcore.Syntax.Parser.FileItemsTotalityProperties
import Solcore.Syntax.Parser.Properties

/-! Conditional totality at the public syntax-parser boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Every valid lexer result produces a public parser output.  Preflight validity
rules out its error branch, nesting overflow is an ordinary diagnostic output,
and the complete-file branch uses the single item-parser premise.
-/
theorem parseLexed_exists_ok_of_validFor
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file) :
    ∃ output, parseLexed file lexed = .ok output := by
  unfold parseLexed
  rw [validateLexed_validFor_ok file lexed lexedValid]
  cases nesting : checkNesting lexed.tokens with
  | some diagnostic =>
      dsimp only
      exact ⟨_, rfl⟩
  | none =>
      dsimp only
      have initialValid := State.initial_validFor lexedValid
      rcases FileInternals.sourceFile_exists_ok itemInvariantFree
          lexed.comments (State.initial file lexed) initialValid with
        ⟨parsed, final, grammar⟩
      simp only [grammar]
      exact ⟨_, rfl⟩

/-- No parser invariant can escape from valid already-tokenized input. -/
theorem parseLexed_ne_error_of_validFor
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file) (error : ParserInvariantError) :
    parseLexed file lexed ≠ .error error := by
  intro failed
  rcases parseLexed_exists_ok_of_validFor itemInvariantFree file lexed
      lexedValid with ⟨output, parsed⟩
  rw [parsed] at failed
  contradiction

/-- Public source parsing returns an output for every source file. -/
theorem parse_exists_ok
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) :
    ∃ output, parse file = .ok output := by
  rcases Lexer.lex_total_validFor file with
    ⟨lexed, lexing, lexedValid⟩
  rcases parseLexed_exists_ok_of_validFor itemInvariantFree file lexed
      lexedValid with ⟨output, parsing⟩
  unfold parse
  simp only [lexing, parsing]
  exact ⟨output, rfl⟩

/-- Under the item premise, no public syntax invariant error is reachable. -/
theorem parse_ne_error
    (itemInvariantFree : FileInternals.ParseItemsItemInvariantFree)
    (file : SourceFile) (error : SyntaxInvariantError) :
    parse file ≠ .error error := by
  intro failed
  rcases parse_exists_ok itemInvariantFree file with ⟨output, parsed⟩
  rw [parsed] at failed
  contradiction

end Solcore.Syntax.Parser
