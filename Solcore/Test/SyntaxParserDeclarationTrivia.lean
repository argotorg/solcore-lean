import Solcore.Syntax.Parser

/-! Nested declaration and enum-constructor comment regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def triviaSource : SourceId := {
  origin := .main
  path := "parser-declaration-trivia.sol"
}

private def assertEqual {α : Type} [BEq α] [Repr α]
    (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := triviaSource, content }
  match Parser.parse file with
  | .error error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      pure output

private def commentTexts (comments : List Comment) : List String :=
  comments.map (·.text)

private def constructorComments
    (declaration : EnumDecl) : List (String × List String) :=
  declaration.value.constructors.map fun constructor =>
    (constructor.value.name.value,
      commentTexts constructor.value.leadingComments)

private def testMethodAndContractComments : IO Unit := do
  let output ← checkedParse "nested declaration comments" (String.intercalate "\n" [
    "trait Read<a> {",
    "  // trait method",
    "  function read(value: a) returns (a);",
    "}",
    "impl Read<word> {",
    "  // impl method",
    "  function read(value: word) returns (word) { value }",
    "}",
    "contract Store {",
    "  // contract field",
    "  value: word;",
    "  // contract function",
    "  function read() returns (word) { value }",
    "}"
  ])
  assertEqual output.parseDiagnostics []
    "nested declaration diagnostics"
  match output.parsed.items with
  | [
      { value := .trait traitDeclaration, .. },
      { value := .impl implDeclaration, .. },
      { value := .contract contractDeclaration, .. }
    ] =>
      match traitDeclaration.value.methods with
      | [method] =>
          assertEqual (commentTexts method.value.leadingComments)
            [" trait method"] "trait method comments"
      | methods => throw (IO.userError
          s!"trait method count changed: {reprStr methods}")
      match implDeclaration.value.methods with
      | [method] =>
          assertEqual (commentTexts method.value.leadingComments)
            [" impl method"] "impl method comments"
      | methods => throw (IO.userError
          s!"impl method count changed: {reprStr methods}")
      match contractDeclaration.value.members with
      | [field, function] =>
          assertEqual (commentTexts field.leadingComments)
            [" contract field"] "contract field comments"
          assertEqual (commentTexts function.leadingComments)
            [" contract function"] "contract function comments"
      | members => throw (IO.userError
          s!"contract member count changed: {reprStr members}")
  | items => throw (IO.userError
      s!"nested declaration items changed: {reprStr items}")

private def testConstructorIntroducers : IO Unit := do
  let output ← checkedParse "constructor introducers" (String.intercalate "\n" [
    "enum Top { // top first after brace",
    "  First",
    "  // top before comma one",
    "  /* top before comma two */",
    "  , // top second after comma",
    "    Second",
    "}",
    "enum BraceChain",
    "// before brace one",
    "/* before brace two */",
    "{ Only }",
    "contract C {",
    "  enum Nested { // local first after brace",
    "    LocalFirst",
    "    // local before comma",
    "    , // local second after comma",
    "      LocalSecond",
    "  }",
    "}"
  ])
  assertEqual output.parseDiagnostics [] "constructor introducer diagnostics"
  match output.parsed.items with
  | [
      { value := .enum top, .. },
      { value := .enum braceChain, .. },
      { value := .contract contract, .. }
    ] =>
      assertEqual (constructorComments top) [
        ("First", [" top first after brace"]),
        ("Second", [
          " top before comma one",
          " top before comma two ",
          " top second after comma"
        ])
      ] "top constructor comments"
      assertEqual (constructorComments braceChain) [
        ("Only", [" before brace one", " before brace two "])
      ] "pre-brace constructor chain"
      match contract.value.members with
      | [{ value := .enum nested, .. }] =>
          assertEqual (constructorComments nested) [
            ("LocalFirst", [" local first after brace"]),
            ("LocalSecond", [
              " local before comma", " local second after comma"
            ])
          ] "contract enum constructor comments"
      | members => throw (IO.userError
          s!"nested enum member changed: {reprStr members}")
  | items => throw (IO.userError
      s!"constructor introducer items changed: {reprStr items}")

private def testConstructorBoundaries : IO Unit := do
  let output ← checkedParse "constructor comment boundaries"
    (String.intercalate "\n" [
      "enum Boundary {",
      "  First // code owns this comment",
      "  , Second",
      "  // blank before comma",
      "",
      "  , Third",
      "  , // blank after comma",
      "",
      "    Fourth",
      "}",
      "contract C {",
      "  enum Nested {",
      "    LocalFirst // local code owns this comment",
      "    , LocalSecond",
      "  }",
      "}"
    ])
  assertEqual output.parseDiagnostics [] "constructor boundary diagnostics"
  match output.parsed.items with
  | [
      { value := .enum boundary, .. },
      { value := .contract contract, .. }
    ] =>
      assertEqual (constructorComments boundary) [
        ("First", []), ("Second", []), ("Third", []), ("Fourth", [])
      ] "blank-line and same-line constructor boundaries"
      match contract.value.members with
      | [{ value := .enum nested, .. }] =>
          assertEqual (constructorComments nested) [
            ("LocalFirst", []), ("LocalSecond", [])
          ] "contract constructor code boundary"
      | members => throw (IO.userError
          s!"contract boundary members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"constructor boundary items changed: {reprStr items}")

private def testDeclarationBoundaries : IO Unit := do
  let output ← checkedParse "nested declaration boundaries"
    (String.intercalate "\n" [
      "trait T<a> {",
      "  function first(value: a); // trailing method",
      "  function second(value: a);",
      "  // detached method",
      "",
      "  function third(value: a);",
      "}",
      "impl T<word> {",
      "  function first(value: word) {} // trailing impl method",
      "  function second(value: word) {}",
      "}",
      "contract C {",
      "  first: word; // trailing field",
      "  second: word;",
      "  function firstFn() {} // trailing function",
      "  function secondFn() {}",
      "}"
    ])
  assertEqual output.parseDiagnostics [] "nested boundary diagnostics"
  match output.parsed.items with
  | [
      { value := .trait traitDeclaration, .. },
      { value := .impl implDeclaration, .. },
      { value := .contract contractDeclaration, .. }
    ] =>
      assertEqual (traitDeclaration.value.methods.map fun method =>
        commentTexts method.value.leadingComments) [[], [], []]
        "trait comment boundaries"
      assertEqual (implDeclaration.value.methods.map fun method =>
        commentTexts method.value.leadingComments) [[], []]
        "impl comment boundaries"
      assertEqual (contractDeclaration.value.members.map fun member =>
        commentTexts member.leadingComments) [[], [], [], []]
        "contract comment boundaries"
  | items => throw (IO.userError
      s!"nested boundary items changed: {reprStr items}")

private def testContractRecoveryComment : IO Unit := do
  let output ← checkedParse "contract recovery comment" (String.intercalate "\n" [
    "contract C {",
    "  // invalid contract item",
    "  unknown nested;",
    "  function valid() {}",
    "}"
  ])
  assertEqual output.parseDiagnostics.length 1
    "contract recovery diagnostic count"
  match output.parsed.items with
  | [{ value := .contract declaration, .. }] =>
      match declaration.value.members with
      | [errorMember, validMember] =>
          assertEqual errorMember.value .error "contract recovery member"
          assertEqual (commentTexts errorMember.leadingComments)
            [" invalid contract item"] "contract recovery comments"
          assertEqual validMember.leadingComments []
            "contract recovery comment leakage"
      | members => throw (IO.userError
          s!"contract recovery members changed: {reprStr members}")
  | items => throw (IO.userError
      s!"contract recovery items changed: {reprStr items}")

/-- Run canonical nested-declaration comment regressions. -/
def testSyntaxParserDeclarationTrivia : IO Unit := do
  testMethodAndContractComments
  testConstructorIntroducers
  testConstructorBoundaries
  testDeclarationBoundaries
  testContractRecoveryComment

end Tests
