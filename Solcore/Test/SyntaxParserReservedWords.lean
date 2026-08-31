import Solcore.Syntax.Parser

/-! Reserved-word conformance tests mirrored from the pinned Rust parser. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def reservedSource (name : String) : SourceId := {
  origin := .main
  path := name ++ ".sol"
}

private def parse (name source : String) : IO ParseOutput := do
  let file : SourceFile := { id := reservedSource name, content := source }
  match Parser.parse file with
  | .ok output => pure output
  | .error error => throw (IO.userError
      s!"{name}: parser invariant failed: {reprStr error}")

private def assertAccepted (name source : String) : IO Unit := do
  let output ← parse name source
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: unexpected lexical diagnostics: " ++
        reprStr output.lexicalDiagnostics))
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: unexpected parse diagnostics: " ++
        reprStr output.parseDiagnostics))

private def assertRejectedIdentifier (name source : String) : IO Unit := do
  let output ← parse name source
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{name}: reserved word should lex without lexical errors: " ++
        reprStr output.lexicalDiagnostics))
  if output.parseDiagnostics.isEmpty then
    throw (IO.userError
      s!"{name}: reserved identifier parsed without diagnostics")

private def testValuesPatternsAndFallbackEntry : IO Unit :=
  assertAccepted "reserved-positive" "
function flip(value: bool) returns (bool) {
  match (value) {
    case true { return false; }
    case false { return true; }
  }
}

contract C {
  fallback() payable {}
}
"

private def testReservedIdentifiers : IO Unit := do
  for (name, source) in [
      ("function-true", "function true() {}"),
      ("function-false", "function false() {}"),
      ("ordinary-function-fallback",
        "contract C { function fallback() {} }"),
      ("let-true", "function f() { let true = false; }"),
      ("field-false", "contract C { false: word; }"),
      ("parameter-fallback", "function f(fallback: word) {}"),
      ("type-true", "function f(value: true) {}"),
      ("import-false", "import {false} from std;"),
      ("enum-fallback", "enum fallback { Value }")
    ] do
    assertRejectedIdentifier name source

/-- Run canonical reserved-word parser regressions. -/
def testSyntaxParserReservedWords : IO Unit := do
  testValuesPatternsAndFallbackEntry
  testReservedIdentifiers

end Tests
