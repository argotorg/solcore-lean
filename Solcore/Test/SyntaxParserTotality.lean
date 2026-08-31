import Solcore.Syntax.Parser

/-!
Deterministic resource and totality regressions corresponding to the pinned
`solcore-rs` parser property tests.  The corpus is generated locally so the
test remains reproducible and does not require a property-testing runtime.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def totalitySource : SourceId := {
  origin := .main
  path := "parser-totality.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def assertValidOutput (label content : String)
    (output : ParseOutput) : IO Unit := do
  let file : SourceFile := { id := totalitySource, content }
  assertEqual output.parsed.source file.id s!"{label} parsed source"
  assertEqual output.parsed.span (SourceSpan.fullFile file)
    s!"{label} parsed file span"
  unless output.tokens.all (fun token => token.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid token span")
  unless output.parsed.comments.all
      (fun comment => comment.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid comment span")
  unless output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid top-item span")
  unless output.lexicalDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid lexical diagnostic span")
  unless output.parseDiagnostics.all
      (fun diagnostic => diagnostic.span.isValidFor file) do
    throw (IO.userError s!"{label}: invalid parse diagnostic span")

private def parseTotal (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := totalitySource, content }
  match Parser.parse file with
  | .ok output =>
      assertValidOutput label content output
      pure output
  | .error error => throw (IO.userError
      s!"{label}: public parser exposed an executor invariant: {reprStr error}")

private def nextSeed (state : Nat) : Nat :=
  (state * 1664525 + 1013904223) % 4294967291

private def nul : Char := Char.ofNat 0

private def characterAlphabet : List Char :=
  ("abcXYZ_019 #$@{}[]()<>+-*/%&|^!~=?:;,.\"\\\n\r\t").toList ++
    [nul, 'λ', 'δ', 'é', 'ß', '漢', '界', '🦀', '🙂', '́']

private def generatedCharacters : Nat → Nat → List Char
  | 0, _ => []
  | length + 1, state =>
      let next := nextSeed state
      let character :=
        characterAlphabet[next % characterAlphabet.length]?.getD nul
      character :: generatedCharacters length next

private def generatedSource (index : Nat) : String :=
  let length := (index * 37 + 11) % 97
  String.ofList (generatedCharacters length (index + 1))

private def edgeSources : List String := [
  "",
  "\n\r\t",
  String.ofList [nul],
  String.ofList ['a', nul, 'b', '\n', 'λ'],
  "§§§",
  "λ δ é ß 漢字 🦀 🙂",
  "́́́",
  "\\ \" ' # $ @",
  "/* unterminated λ",
  "// comment without newline",
  "\"bad\\qescape\"",
  "0x 0b 0o 123_ 1e+",
  "(((([[{{ ?? :: ;;;",
  "}}]]) ) else default return",
  "function nul() { let x = " ++ String.ofList [nul] ++ "; }"
]

private def testGeneratedUtf8Totality : IO Unit := do
  for (source, index) in edgeSources.zipIdx do
    let _ ← parseTotal s!"UTF-8 edge {index}" source
  for index in List.range 192 do
    let source := generatedSource index
    let _ ← parseTotal s!"generated UTF-8 {index}" source

private def fixture (lines : List String) : String :=
  String.intercalate "\n" lines ++ "\n"

private def corpusSeeds : List (String × String) := [
  ("valid function", "function ok() {}\n"),
  ("valid contract", fixture [
    "contract Modifiers {",
    "  constructor() {}",
    "  function ping() public {}",
    "  function deposit() public payable returns (uint256) { return 0; }",
    "  fallback() payable {}",
    "}"
  ]),
  ("valid match", fixture [
    "function main(foo: (word, word)) returns (word) {",
    "  let res: word;",
    "  match (foo) { case (v0, v1) {",
    "    { let x: word = v1; res = x; }",
    "  } }",
    "  return res;",
    "}"
  ]),
  ("invalid signature", "function main( -> word { return 0; }\n"),
  ("invalid body", "function broken() { let x = ; return pair(+ -, 0);\n"),
  ("invalid comment", "contract C { /* unclosed\n")
]

private def mutations : List String := [
  "",
  "§",
  String.ofList [nul],
  "/*",
  "\"bad\\q\"",
  " ? : ",
  "\nreturn;\n",
  "λ🦀",
  "((((([",
  "}}];"
]

private def insertMutation (source mutation : String)
    (position : Nat) : String :=
  let characters := source.toList
  let offset := position % (characters.length + 1)
  String.ofList
    (characters.take offset ++ mutation.toList ++ characters.drop offset)

private def insertionPositions (seedIndex mutationIndex length : Nat) : List Nat :=
  [0, length / 2, length,
    (seedIndex * 31 + mutationIndex * 17 + 7) % (length + 1)]

private def testCorpusMutationTotality : IO Unit := do
  for ((seedName, source), seedIndex) in corpusSeeds.zipIdx do
    for (mutation, mutationIndex) in mutations.zipIdx do
      for (position, positionIndex) in
          (insertionPositions seedIndex mutationIndex source.length).zipIdx do
        let mutated := insertMutation source mutation position
        let label :=
          s!"mutation {seedName}/{mutationIndex}/{positionIndex}"
        let _ ← parseTotal label mutated

private def repeatText (count : Nat) (text : String) : String :=
  (List.replicate count text).foldl (· ++ ·) ""

private def rightNestedTernary (depth : Nat) : String :=
  "function main() returns (word) { return " ++
    repeatText depth "true ? 0 : " ++ "0; }"

private def nestedType (depth : Nat) : String :=
  "type Deep = " ++ String.ofList (List.replicate depth '(') ++ "word" ++
    String.ofList (List.replicate depth ')') ++ ";"

private def testResourceBoundaries : IO Unit := do
  -- As upstream intends, syntax parsing of this chain completes before a later
  -- HIR expression-depth policy is applied.
  let ternary ← parseTotal "right-nested ternary depth 96"
    (rightNestedTernary 96)
  assertEqual ternary.lexicalDiagnostics [] "ternary lexical diagnostics"
  assertEqual ternary.parseDiagnostics [] "ternary parse diagnostics"
  assertEqual ternary.parsed.items.length 1 "ternary item count"

  let ternaryBoundary ← parseTotal "right-nested ternary at syntax limit"
    (rightNestedTernary Parser.maxSyntaxNesting)
  assertEqual ternaryBoundary.lexicalDiagnostics []
    "ternary boundary lexical diagnostics"
  assertEqual ternaryBoundary.parseDiagnostics []
    "ternary boundary parse diagnostics"
  assertEqual ternaryBoundary.parsed.items.length 1
    "ternary boundary item count"

  let boundary ← parseTotal "delimiter nesting at limit"
    (nestedType Parser.maxSyntaxNesting)
  assertEqual boundary.lexicalDiagnostics [] "boundary lexical diagnostics"
  assertEqual boundary.parseDiagnostics [] "boundary parse diagnostics"
  assertEqual boundary.parsed.items.length 1 "boundary item count"

  let overflow ← parseTotal "delimiter nesting above limit"
    (nestedType (Parser.maxSyntaxNesting + 1))
  assertEqual overflow.parsed.items.length 0 "overflow item count"
  match overflow.parseDiagnostics with
  | [{ kind := .nestingExceeded .delimiter limit, .. }] =>
      assertEqual limit Parser.maxSyntaxNesting "reported nesting limit"
  | diagnostics => throw (IO.userError
      s!"overflow diagnostics changed: {reprStr diagnostics}")

/-- Run deterministic arbitrary-source, mutation, and resource regressions. -/
def testSyntaxParserTotality : IO Unit := do
  testGeneratedUtf8Totality
  testCorpusMutationTotality
  testResourceBoundaries

end Tests
