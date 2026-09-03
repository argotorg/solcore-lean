import Solcore.Syntax.Parser.PublicSingleRecoveryOutputProperties

/-! Independent root-recovery and cascade derivations determine all fields of
public parse outputs. Both retained and suppressed recovery events are checked. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicSingleRecoveryOutputProperties

open Solcore
open Solcore.Syntax
open Solcore.Syntax.Parser

variable {file : SourceFile} {lexed : LexedFile} {item : TopItem}
  {after : DeclarativeGrammar.Remainder} {kept : List SourceSpan}
  (accepted : DeclarativeGrammar.LexedFileValidationAccepts file lexed)
  (clears : DeclarativeGrammar.NestingClears lexed.tokens)
  (startsAbsent : DeclarativeGrammar.TopItemKindsAbsentAt
    (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens)
    DeclarativeGrammar.ImportTerminatorTopItemStartKinds)
  (recovered : DeclarativeGrammar.TopItemRecoveryParses
    (DeclarativeGrammar.sourceFileRootRemainder lexed.tokens) item after)
  (atEnd : after.cursor = lexed.tokens.length)

example (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) [item.span] kept) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := [Trivia.attachTopItemComments file lexed.comments item]
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := FileInternals.topItemRecoveryDiagnostics kept
    } :=
  parseLexed_eq_ok_of_singleRecoveryToEnd accepted clears startsAbsent
    recovered atEnd filtered

example (result : parseLexed file lexed =
    .ok (singleRecoveryParseOutput file lexed item kept)) :
    DeclarativeGrammar.LexedFileValidationAccepts file lexed ∧
      DeclarativeGrammar.LexicalCascadeFilters file.content
        (lexed.diagnostics.map (·.span)) [item.span] kept :=
  (parseLexed_eq_ok_singleRecovery_iff clears startsAbsent recovered atEnd).mp
    result

example (suppressed : DeclarativeGrammar.LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) item.span) :
    parseLexed file lexed = .ok (singleRecoveryParseOutput file lexed item []) :=
  parseLexed_eq_ok_of_singleRecoveryToEnd accepted clears startsAbsent
    recovered atEnd (.drop suppressed .nil)

example (retained : ¬ DeclarativeGrammar.LexicalCascadeSuppresses file.content
    (lexed.diagnostics.map (·.span)) item.span) :
    parseLexed file lexed =
      .ok (singleRecoveryParseOutput file lexed item [item.span]) :=
  parseLexed_eq_ok_of_singleRecoveryToEnd accepted clears startsAbsent
    recovered atEnd (.keep retained .nil)

example (lexing : Lexer.lex file = .ok lexed)
    (filtered : DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [item.span] kept) :
    parse file = .ok (singleRecoveryParseOutput file lexed item kept) :=
  parse_eq_ok_of_singleRecoveryToEnd lexing clears startsAbsent
    recovered atEnd filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (singleRecoveryParseOutput file lexed item kept)) :
    DeclarativeGrammar.LexicalCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) [item.span] kept :=
  (parse_eq_ok_singleRecovery_iff lexing clears startsAbsent recovered atEnd).mp
    result

end Solcore.Test.SyntaxParserPublicSingleRecoveryOutputProperties
