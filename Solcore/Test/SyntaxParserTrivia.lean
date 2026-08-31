import Solcore.Syntax.Parser

/-! Leading-comment fidelity regressions for canonical syntax parsing. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def triviaSource : SourceId := {
  origin := .main
  path := "parser-trivia.sol"
}

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := triviaSource, content }
  match Parser.parse file with
  | .ok output => pure output
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private def leadingTexts (item : TopItem) : List String :=
  item.leadingComments.map (·.text)

private def itemAt (label : String) (output : ParseOutput)
    (index : Nat) : IO TopItem :=
  match output.parsed.items[index]? with
  | some item => pure item
  | none => throw (IO.userError
      s!"{label}: missing item {index}, only {output.parsed.items.length} present")

private def testAdjacentComments : IO Unit := do
  let output ← checkedParse "CRLF comments"
    "// one\r\n/* two */\r\ntype A = word;"
  let item ← itemAt "CRLF comments" output 0
  assertEqual (leadingTexts item) [" one\r", " two "]
    "CRLF attached comments"

  let adjacent ← checkedParse "adjacent comments"
    "/*a*//*b*/\ntype A = word;"
  let adjacentItem ← itemAt "adjacent comments" adjacent 0
  assertEqual (leadingTexts adjacentItem) ["a", "b"]
    "adjacent attached comments"

private def testBlankLineBoundary : IO Unit := do
  let blank ← checkedParse "blank line"
    "/* doc */\r\n\r\ntype A = word;"
  let blankItem ← itemAt "blank line" blank 0
  assertEqual blankItem.leadingComments [] "blank-line attachment"

  let suffix ← checkedParse "newest comment suffix"
    "// old\n\n// new\ntype A = word;"
  let suffixItem ← itemAt "newest comment suffix" suffix 0
  assertEqual (leadingTexts suffixItem) [" new"]
    "newest direct comment suffix"

private def testCodeBeforeComment : IO Unit := do
  let trailing ← checkedParse "trailing comment"
    "type A = word; // trailing\r\ntype B = word;"
  let first ← itemAt "trailing comment" trailing 0
  let second ← itemAt "trailing comment" trailing 1
  assertEqual first.leadingComments [] "first leading comments"
  assertEqual second.leadingComments [] "trailing comment leakage"

  let code ← checkedParse "code before comments"
    "junk /*a*/ /*b*/\ntype A = word;"
  let declaration ← itemAt "code before comments" code 1
  assertEqual declaration.leadingComments [] "code-before attachment"

  let multiline ← checkedParse "multiline closing tail"
    "/* multi\n*/ /* b */\ntype A = word;"
  let multilineItem ← itemAt "multiline closing tail" multiline 0
  assertEqual multilineItem.leadingComments []
    "multiline closing-tail attachment"

private def testRustUnicodeWhitespace : IO Unit := do
  let nbsp ← checkedParse "nonbreaking space"
    "/*doc*/\u00a0type A = word;"
  let nbspItem ← itemAt "nonbreaking space" nbsp 0
  assertEqual (leadingTexts nbspItem) ["doc"] "NBSP attachment"
  assertEqual nbsp.lexicalDiagnostics.length 1 "NBSP lexical diagnostic"

  let separators ← checkedParse "Unicode separators"
    "/*doc*/\u2028\u2028type A = word;"
  let separatorItem ← itemAt "Unicode separators" separators 0
  assertEqual (leadingTexts separatorItem) ["doc"]
    "Unicode separator attachment"
  assertEqual separators.lexicalDiagnostics.length 2
    "Unicode separator lexical diagnostics"

  let zeroWidth ← checkedParse "zero-width space"
    "/*doc*/\u200btype A = word;"
  let zeroWidthItem ← itemAt "zero-width space" zeroWidth 0
  assertEqual zeroWidthItem.leadingComments []
    "zero-width non-whitespace attachment"

private def testRecoveryOwnership : IO Unit := do
  let output ← checkedParse "recovery comments"
    "// recovery\n+ -; type B = word;"
  let recovered ← itemAt "recovery comments" output 0
  let declaration ← itemAt "recovery comments" output 1
  assertEqual (leadingTexts recovered) [" recovery"]
    "recovery item leading comment"
  assertEqual declaration.leadingComments []
    "recovery comment did not leak"

private def forgedLexed (file : SourceFile)
    (comments : List Comment) : LexedFile := {
  source := file.id
  tokens := []
  comments
  diagnostics := []
}

private def forgedComment (file : SourceFile)
    (startByte endByte : Nat) : Comment := {
  kind := .block
  text := ""
  span := { source := file.id, startByte, endByte }
}

private def expectInvalidSecondComment (label : String)
    (file : SourceFile) (comments : List Comment) : IO Unit :=
  match Parser.parseLexed file (forgedLexed file comments) with
  | .error (.invalidCommentSpan 1 _) => pure ()
  | result => throw (IO.userError
      s!"{label}: expected second-comment invariant, got {reprStr result}")

private def testForgedCommentOrder : IO Unit := do
  let file : SourceFile := {
    id := triviaSource
    content := "abcdefghijklmnop"
  }
  expectInvalidSecondComment "out-of-order comments" file [
    forgedComment file 5 7,
    forgedComment file 2 4
  ]
  expectInvalidSecondComment "overlapping comments" file [
    forgedComment file 2 6,
    forgedComment file 5 8
  ]

/-- Run canonical parser leading-comment regressions. -/
def testSyntaxParserTrivia : IO Unit := do
  testAdjacentComments
  testBlankLineBoundary
  testCodeBeforeComment
  testRustUnicodeWhitespace
  testRecoveryOwnership
  testForgedCommentOrder

end Tests
