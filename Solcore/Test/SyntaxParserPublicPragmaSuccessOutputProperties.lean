import Solcore.Syntax.Parser.PublicPragmaSuccessOutputProperties

/-! Consumers of complete pragma outputs from independent AST/trace grammar.
All reports, their order, and their multiplicity remain part of the result. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPublicPragmaSuccessOutputProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {file : SourceFile} {lexed : LexedFile} {declaration : PragmaDecl}
  {after : Remainder} {trace kept : List ParseDiagnostic}
  (accepted : LexedFileValidationAccepts file lexed)
  (clears : NestingClears lexed.tokens)
  (parsed : PragmaDeclTraceParses (sourceFileRootRemainder lexed.tokens)
    declaration after trace)
  (atEnd : after.cursor = lexed.tokens.length)

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) :
    parseLexed file lexed = .ok {
      parsed := {
        source := file.id
        span := SourceSpan.fullFile file
        items := [Trivia.attachTopItemComments file lexed.comments
          (FileInternals.wrapPragma declaration)]
        comments := lexed.comments
      }
      tokens := lexed.tokens
      lexicalDiagnostics := lexed.diagnostics
      parseDiagnostics := kept
    } :=
  parseLexed_eq_ok_of_singlePragma accepted clears parsed atEnd filtered

example (result : parseLexed file lexed =
    .ok (singlePragmaParseOutput file lexed declaration kept)) :
    LexedFileValidationAccepts file lexed ∧
      ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace kept :=
  (parseLexed_eq_ok_singlePragma_iff clears parsed atEnd).mp result

example (lexing : Lexer.lex file = .ok lexed)
    (filtered : ParseDiagnosticCascadeFilters file.content
      (lexed.diagnostics.map (·.span)) trace kept) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration kept) :=
  parse_eq_ok_of_singlePragma lexing clears parsed atEnd filtered

example (lexing : Lexer.lex file = .ok lexed)
    (result : parse file = .ok (singlePragmaParseOutput file lexed declaration kept)) :
    ParseDiagnosticCascadeFilters file.content (lexed.diagnostics.map (·.span)) trace kept :=
  (parse_eq_ok_singlePragma_iff lexing clears parsed atEnd).mp result

example : parseLexed file lexed =
    .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parseLexed_eq_ok_of_singlePragmaTrace accepted clears parsed atEnd

example (lexing : Lexer.lex file = .ok lexed) :
    parse file = .ok (singlePragmaParseOutput file lexed declaration trace) :=
  parse_eq_ok_of_singlePragmaTrace lexing clears parsed atEnd

example (filtered : ParseDiagnosticCascadeFilters file.content
    (lexed.diagnostics.map (·.span)) trace kept) : kept = trace :=
  filtered.output_unique (parsed.cascadeFilters file.content (lexed.diagnostics.map (·.span)))

example {names : List Identifier} {events : List ParseDiagnostic}
    (diagnostics : IdentifierListDiagnosticTrace names events)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical events events :=
  diagnostics.cascadeFilters source lexical

end Solcore.Test.SyntaxParserPublicPragmaSuccessOutputProperties
