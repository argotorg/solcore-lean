import Solcore.Syntax.Parser.UnexpectedDiagnosticCascadeProperties

/-! Consumers retain the complete expectation metadata across cascade filtering. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserUnexpectedDiagnosticCascadeProperties

open Solcore
open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan)
    (filtered : LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
      unexpectedDiagnostics found expected context kept :=
  (filterParseDiagnostics_unexpected_iff file lexical found expected context raw kept).mp
    filtered

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan)
    (result : filterParseDiagnostics file lexical
      (unexpectedDiagnostics found expected context raw) =
        unexpectedDiagnostics found expected context kept) :
    LexicalCascadeFilters file.content (lexical.map (·.span)) raw kept :=
  (filterParseDiagnostics_unexpected_iff file lexical found expected context raw kept).mpr
    result

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (span : SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [{ span, kind := .unexpected found expected context }] =
      [{ span, kind := .unexpected found expected context }] :=
  filterParseDiagnostics_unexpected_of_filters file lexical found expected context
    (.keep retained .nil)

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (span : SourceSpan)
    (suppressed : LexicalCascadeSuppresses file.content (lexical.map (·.span)) span) :
    filterParseDiagnostics file lexical [{ span, kind := .unexpected found expected context }] =
      [] :=
  filterParseDiagnostics_unexpected_of_filters file lexical found expected context
    (.drop suppressed .nil)

end Solcore.Test.SyntaxParserUnexpectedDiagnosticCascadeProperties
