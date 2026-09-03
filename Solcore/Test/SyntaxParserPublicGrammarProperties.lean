import Solcore.Syntax.Parser.PublicSourceFileGrammarProperties

/-! Independent grammar consumers, deliberately assuming no parser reply. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicGrammarProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

example (file : SourceFile) (lexed : LexedFile)
    (accepted : LexedFileValidationAccepts file lexed) :
    ∃ parsed,
      PublicSourceFileOrdinaryParses file lexed.tokens lexed.comments parsed ∧
      ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file parsed ∧
      ∀ other, PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments other → other = parsed := by
  rcases publicSourceFileOrdinary_exists_unique_of_validation file lexed accepted with
    ⟨parsed, derivation, unique⟩
  exact ⟨parsed, derivation, derivation.validFor_of_validation accepted, unique⟩

example {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (lexing : Lexer.lex file = .ok lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    parsed.source = file.id ∧ parsed.span.ValidFor file := by
  have valid := derivation.validFor_of_lexing lexing
  exact ⟨valid.1, valid.2.1⟩

example {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (accepted : LexedFileValidationAccepts file lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∀ item ∈ parsed.items,
      TopItem.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor file item :=
  (derivation.validFor_of_validation accepted).2.2.1

example {file : SourceFile} {lexed : LexedFile} {parsed : ParsedFile}
    (accepted : LexedFileValidationAccepts file lexed)
    (derivation : PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∀ comment ∈ parsed.comments, comment.span.ValidFor file :=
  (derivation.validFor_of_validation accepted).2.2.2

end Solcore.Test.SyntaxParserPublicGrammarProperties
