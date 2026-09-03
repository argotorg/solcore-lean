import Solcore.Syntax.Parser.PublicParseCompletenessProperties

/-! Independent forward and reverse consumers of complete public syntax parsing. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSourceFileCompletenessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @FileInternals.sourceFile_ordinary_iff_exists_ok_of_topItem
example := @FileInternals.sourceFile_ordinary_iff_exists_ok
example := @parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @parseLexed_exists_ok_iff_publicSourceFileOrdinary
example := @parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @parse_exists_ok_iff_publicSourceFileOrdinary

example (comments : List Comment) {input : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile} {afterParsed : DeclarativeGrammar.Remainder}
    (expected : DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsed afterParsed) :
    ∃ output, sourceFile comments input = .ok parsed output ∧
      output.declarativeRemainder = afterParsed :=
  (FileInternals.sourceFile_ordinary_iff_exists_ok comments inputValid).mp expected

example (comments : List Comment) {input output : State} (inputValid : input.ValidFor)
    {parsed : ParsedFile}
    (result : sourceFile comments input = .ok parsed output) :
    DeclarativeGrammar.SourceFileOrdinaryParses input.file comments
      input.declarativeRemainder parsed output.declarativeRemainder :=
  (FileInternals.sourceFile_ordinary_iff_exists_ok comments inputValid).mpr
    ⟨output, result, rfl⟩

example (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile)
    (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
    (expected : DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∃ output, parseLexed file lexed = .ok output ∧ output.parsed = parsed :=
  (parseLexed_exists_ok_iff_publicSourceFileOrdinary file lexed parsed).mpr
    ⟨accepted, expected⟩

example (file : SourceFile) (lexed : LexedFile) {output : ParseOutput}
    (result : parseLexed file lexed = .ok output) :
    DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
      DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed :=
  (parseLexed_exists_ok_iff_publicSourceFileOrdinary file lexed output.parsed).mp
    ⟨output, result, rfl⟩

example (file : SourceFile) (lexed : LexedFile) (parsed : ParsedFile)
    (lexing : Lexer.lex file = .ok lexed)
    (expected : DeclarativeGrammar.PublicSourceFileOrdinaryParses file
      lexed.tokens lexed.comments parsed) :
    ∃ output, parse file = .ok output ∧ output.parsed = parsed :=
  (parse_exists_ok_iff_publicSourceFileOrdinary file parsed).mpr
    ⟨lexed, lexing, expected⟩

example (file : SourceFile) {output : ParseOutput}
    (result : parse file = .ok output) :
    ∃ lexed, Lexer.lex file = .ok lexed ∧
      DeclarativeGrammar.PublicSourceFileOrdinaryParses file
        lexed.tokens lexed.comments output.parsed :=
  (parse_exists_ok_iff_publicSourceFileOrdinary file output.parsed).mp
    ⟨output, result, rfl⟩

end Solcore.Test.SyntaxParserSourceFileCompletenessProperties
