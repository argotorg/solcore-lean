import Solcore.Syntax.Parser

/-!
Focused compatibility-boundary regressions for the canonical syntax pinned by
ADR-0153.  These spellings belonged to the replaced frontend or to Solidity;
the canonical parser must diagnose them instead of silently accepting a second
source language.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private structure SpellingCase where
  label : String
  legacy : String
  canonical : String

private def sourceId (label : String) : SourceId := {
  origin := .main
  path := "legacy-rejection-" ++ label ++ ".sol"
}

private def parseTotal (label source : String) : IO ParseOutput := do
  let file : SourceFile := { id := sourceId label, content := source }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: source parsing failed with an invariant error: {reprStr error}")
  | .ok output =>
      unless output.parsed.span.isValidFor file do
        throw (IO.userError s!"{label}: parsed-file span escaped the source")
      unless output.lexicalDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: lexical diagnostic span escaped the source")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: parse diagnostic span escaped the source")
      pure output

private def assertRejected (case : SpellingCase) : IO Unit := do
  let output ← parseTotal (case.label ++ "-legacy") case.legacy
  if output.lexicalDiagnostics.isEmpty && output.parseDiagnostics.isEmpty then
    throw (IO.userError
      s!"{case.label}: legacy spelling parsed without a diagnostic: {case.legacy}")

private def assertCanonicalAccepted (case : SpellingCase) : IO Unit := do
  let output ← parseTotal (case.label ++ "-canonical") case.canonical
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{case.label}: canonical counterpart has lexical diagnostics: " ++
        reprStr output.lexicalDiagnostics))
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"{case.label}: canonical counterpart has parse diagnostics: " ++
        reprStr output.parseDiagnostics))

private def spellingCases : List SpellingCase := [
  {
    label := "data-declaration"
    legacy := "data Option(T) = None;"
    canonical := "enum Option<T> { None }"
  },
  {
    label := "class-declaration"
    legacy := "class Eq(T) {}"
    canonical := "trait Eq<T> {}"
  },
  {
    label := "instance-declaration"
    legacy := "instance Eq: word {}"
    canonical := "impl Eq<word> {}"
  },
  {
    label := "forall-declaration-prefix"
    legacy := "forall T. function id(x: T) -> T { return x; }"
    canonical :=
      "function id<T>(x: T) returns (T) { return x; }"
  },
  {
    label := "prefix-public-function"
    legacy := "public function exposed() -> word { return 0; }"
    canonical :=
      "contract C { function exposed() public returns (word) { return 0; } }"
  },
  {
    label := "arrow-return"
    legacy := "function arrowResult() -> word { return 0; }"
    canonical :=
      "function arrowResult() returns (word) { return 0; }"
  },
  {
    label := "string-import"
    legacy := "import \"old/module.sol\";"
    canonical := "import old.module;"
  },
  {
    label := "postfix-selective-import"
    legacy := "import old.module.{item};"
    canonical := "import {item} from old.module;"
  },
  {
    label := "core-colon-equals-let"
    legacy := "function invalid() { let value := 1; }"
    canonical := "function valid() { let value = 1; }"
  },
  {
    label := "core-colon-equals-assignment"
    legacy := "function invalid() { value := 1; }"
    canonical := "function valid() { let value = 0; value = 1; }"
  },
  {
    label := "nullary-generic-arguments"
    legacy := "function emptyArgs(x: Box<>) {}"
    canonical := "function value<T>(x: Box<T>) {}"
  }
]

private def testLegacyBoundary : IO Unit := do
  for case in spellingCases do
    assertRejected case
    assertCanonicalAccepted case

private def testColonEqualsRemainsYulSyntax : IO Unit := do
  let output ← parseTotal "yul-colon-equals"
    "function valid() { assembly { let value := 1 value := add(value, 1) } }"
  unless output.lexicalDiagnostics.isEmpty && output.parseDiagnostics.isEmpty do
    throw (IO.userError (
      s!"Yul `:=` counterpart was rejected: {reprStr output.lexicalDiagnostics}; " ++
        reprStr output.parseDiagnostics))

/-- Run focused rejection checks for spellings removed by ADR-0153. -/
def testSyntaxParserLegacyRejection : IO Unit := do
  testLegacyBoundary
  testColonEqualsRemainsYulSyntax

end Tests
