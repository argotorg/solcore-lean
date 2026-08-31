import Solcore.Syntax.Parser

/-! Recovery, totality, and resource-bound regressions for canonical parsing. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def parserSource : SourceId := {
  origin := .main
  path := "parser-recovery.sol"
}

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.parsed.source file.id s!"{label} source"
      unless output.parsed.span.isValidFor file do
        throw (IO.userError s!"{label}: invalid file span")
      pure output

private def aliasDecl? (item : TopItem) : Option TypeAliasDecl :=
  match item.value with
  | .typeAlias declaration => some declaration
  | _ => none

private def testTypeRecovery : IO Unit := do
  let output ← checkedParse "type recovery"
    "type A = + - *; type B = word;"
  match output.parsed.items with
  | [first, second] =>
      match aliasDecl? first, aliasDecl? second with
      | some recovered, some valid =>
          match recovered.value.value.value with
          | .error => pure ()
          | value => throw (IO.userError
              s!"type recovery: expected error type, got {reprStr value}")
          assertEqual (byteRange recovered.value.value.span) (9, 14)
            "type recovery error span"
          assertEqual valid.value.name.value "B"
            "type recovery following alias"
      | _, _ => throw (IO.userError "type recovery: expected two aliases")
  | items => throw (IO.userError
      s!"type recovery: expected two items, got {items.length}")
  match output.parseDiagnostics with
  | [unexpected, recovered] =>
      assertEqual (byteRange unexpected.span) (9, 10)
        "type recovery unexpected span"
      assertEqual (byteRange recovered.span) (9, 14)
        "type recovery consumed span"
      match recovered.kind with
      | .recovered .typeAliasValue => pure ()
      | kind => throw (IO.userError
          s!"type recovery: wrong recovery diagnostic {reprStr kind}")
  | diagnostics => throw (IO.userError
      s!"type recovery: expected two diagnostics, got {diagnostics.length}")

private def testUnrecoverableAliases : IO Unit := do
  let empty ← checkedParse "empty alias RHS"
    "type A = ; type B = word;"
  assertEqual empty.parsed.items.length 0 "empty alias item count"
  assertEqual empty.parseDiagnostics.length 1 "empty alias diagnostics"

  let prefixOutput ← checkedParse "prefix-success alias"
    "type A = word garbage; type B = word;"
  assertEqual prefixOutput.parsed.items.length 0 "prefix-success item count"
  match prefixOutput.parseDiagnostics with
  | [diagnostic] =>
      assertEqual (byteRange diagnostic.span) (14, 21)
        "prefix-success failure span"
  | diagnostics => throw (IO.userError
      s!"prefix-success: expected one diagnostic, got {diagnostics.length}")

private def testTopLevelRecovery : IO Unit := do
  let output ← checkedParse "top-level recovery" "+ -; type B = word;"
  match output.parsed.items with
  | [errorItem, aliasItem] =>
      match errorItem.value, aliasDecl? aliasItem with
      | .error, some alias =>
          assertEqual (byteRange errorItem.span) (0, 4)
            "top-level recovery span"
          assertEqual alias.value.name.value "B"
            "top-level recovery following alias"
      | _, _ => throw (IO.userError
          "top-level recovery: wrong recovered item shapes")
  | items => throw (IO.userError
      s!"top-level recovery: expected two items, got {items.length}")

private def nestedNamed : Nat → String
  | 0 => "word"
  | depth + 1 => "Box<" ++ nestedNamed depth ++ ">"

private def testNestingGuards : IO Unit := do
  let openings := String.ofList (List.replicate 129 '(')
  let closings := String.ofList (List.replicate 129 ')')
  let overflow ← checkedParse "delimiter nesting"
    ("type A = " ++ openings ++ "word" ++ closings ++ ";")
  assertEqual overflow.parsed.items.length 0 "nesting overflow items"
  match overflow.parseDiagnostics with
  | [{ span, kind := .nestingExceeded .delimiter 128 }] =>
      assertEqual (byteRange span) (137, 138) "nesting overflow span"
  | diagnostics => throw (IO.userError
      s!"nesting overflow: wrong diagnostics {reprStr diagnostics}")

  let angleDeep ← checkedParse "angle depth"
    ("type A = " ++ nestedNamed 129 ++ ";")
  assertEqual angleDeep.parsed.items.length 1 "angle depth item count"
  assertEqual angleDeep.parseDiagnostics [] "angle depth diagnostics"

private def testValidatedLexedInput : IO Unit := do
  let first : SourceFile := {
    id := parserSource
    content := "type A = word;"
  }
  let second : SourceFile := {
    id := { origin := .external "other", path := "other.sol" }
    content := first.content
  }
  let lexed ← match Lexer.lex first with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"validation lex failed: {reprStr error}")
  match Parser.parseLexed second lexed with
  | .error (.invalidLexedSource expected actual) =>
      assertEqual expected second.id "invalid source expected owner"
      assertEqual actual first.id "invalid source actual owner"
  | result => throw (IO.userError
      s!"invalid source: unexpected result {reprStr result}")

  let invalid : LexedFile := {
    source := first.id
    tokens := [{
      span := { source := first.id, startByte := 0, endByte := 99 }
      value := .identifier "bad"
    }]
    comments := []
    diagnostics := []
  }
  match Parser.parseLexed first invalid with
  | .error (.invalidTokenSpan 0 _) => pure ()
  | result => throw (IO.userError
      s!"invalid token span: unexpected result {reprStr result}")

/-- Run canonical parser recovery and totality regressions. -/
def testSyntaxParserRecovery : IO Unit := do
  testTypeRecovery
  testUnrecoverableAliases
  testTopLevelRecovery
  testNestingGuards
  testValidatedLexedInput

end Tests
