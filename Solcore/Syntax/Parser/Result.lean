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

namespace ParseOutput

/-- The lexer and parser reported no ordinary source diagnostics. -/
def DiagnosticFree (output : ParseOutput) : Prop :=
  output.lexicalDiagnostics = [] ∧ output.parseDiagnostics = []

/-- Executable check for the diagnostic-free parser boundary. -/
def isDiagnosticFree (output : ParseOutput) : Bool :=
  output.lexicalDiagnostics.isEmpty && output.parseDiagnostics.isEmpty

theorem isDiagnosticFree_eq_true_iff (output : ParseOutput) :
    output.isDiagnosticFree = true ↔ output.DiagnosticFree := by
  simp [isDiagnosticFree, DiagnosticFree]

end ParseOutput

/-- Public parser result; only executor invariants inhabit the error branch. -/
abbrev ParseResult := Except SyntaxInvariantError ParseOutput

end Solcore.Syntax
