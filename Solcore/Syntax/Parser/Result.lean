import Solcore.Syntax.Parser.Diagnostic

set_option autoImplicit false

namespace Solcore.Syntax

/--
Total ordinary result of canonical source parsing. Retained tokens make later
span and provenance checks independent of re-lexing the source.
-/
structure ParseOutput where
  parsed : ParsedFile
  tokens : List Token
  lexicalDiagnostics : List LexicalDiagnostic
  parseDiagnostics : List ParseDiagnostic
  deriving Repr, BEq

/-- Public parser result; only executor invariants inhabit the error branch. -/
abbrev ParseResult := Except SyntaxInvariantError ParseOutput

end Solcore.Syntax
