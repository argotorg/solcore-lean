import Solcore

/-! Smoke test for the canonical syntax API exposed by `import Solcore`. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Syntax

private def publicSyntaxSource : SourceFile := {
  id := {
    origin := .main
    path := "public-syntax.sol"
  }
  content := "type PublicWord = word;"
}

private def malformedPublicSyntaxSource : SourceFile := {
  id := {
    origin := .main
    path := "public-syntax-malformed.sol"
  }
  content := "function bad(x: ) {}"
}

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: expected true")

/-- Exercise the canonical source-to-AST API through the repository umbrella. -/
def testSyntaxPublicBoundary : IO Unit := do
  assertTrue (Syntax.isValidIdentifier "PublicWord")
    "public identifier validator"
  match Syntax.Parser.parse publicSyntaxSource with
  | .error error => throw (IO.userError
      s!"public parser invariant failed: {reprStr error}")
  | .ok output =>
      assertTrue output.isDiagnosticFree "public diagnostic-free result"
      unless output.lexicalDiagnostics.isEmpty do
        throw (IO.userError
          s!"unexpected lexical diagnostics: {reprStr output.lexicalDiagnostics}")
      unless output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"unexpected parse diagnostics: {reprStr output.parseDiagnostics}")
      match output.parsed.items with
      | [{ value := .typeAlias declaration, .. }] =>
          let astWitness : TypeAliasDecl := declaration
          assertTrue (astWitness.value.name.value == "PublicWord")
            "public canonical AST"
      | items => throw (IO.userError
          s!"unexpected public AST: {reprStr items}")
  match Syntax.Parser.parse malformedPublicSyntaxSource with
  | .error error => throw (IO.userError
      s!"malformed public parser invariant failed: {reprStr error}")
  | .ok output =>
      assertTrue (!output.isDiagnosticFree)
        "malformed public diagnostic result"

example (output : ParseOutput) :
    output.isDiagnosticFree = true ↔ output.DiagnosticFree :=
  output.isDiagnosticFree_eq_true_iff

end Tests
