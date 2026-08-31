import Solcore.Syntax.Lexer

/-! Canonical Solcore lexer catalog regressions, pinned to solcore-rs PR #20. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def catalogSource : SourceId := {
  origin := .main
  path := "catalog.sol"
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def expectSingle (spelling : String) (expected : TokenKind) : IO Unit := do
  let file : SourceFile := { id := catalogSource, content := spelling }
  match Lexer.lex file with
  | .error diagnostic =>
      throw (IO.userError
        s!"catalog spelling {spelling.quote} exhausted lexer fuel: {reprStr diagnostic}")
  | .ok output =>
      assertTrue output.comments.isEmpty
        s!"catalog spelling {spelling.quote} unexpectedly produced comments"
      assertTrue output.diagnostics.isEmpty
        s!"catalog spelling {spelling.quote} produced {reprStr output.diagnostics}"
      match output.tokens with
      | [token] =>
          assertTrue (token.value == expected)
            s!"catalog spelling {spelling.quote} produced {reprStr token.value}"
          assertTrue
            ((token.span.startByte, token.span.endByte) ==
              (0, spelling.utf8ByteSize))
            s!"catalog spelling {spelling.quote} had span {reprStr token.span}"
          assertTrue (token.span.isValidFor file)
            s!"catalog spelling {spelling.quote} had an invalid UTF-8 span"
      | tokens =>
          throw (IO.userError
            s!"catalog spelling {spelling.quote} produced {tokens.length} tokens")

private def keywordCases : List (String × TokenKind) := [
  ("contract", .keyword .contractKw),
  ("import", .keyword .importKw),
  ("export", .keyword .exportKw),
  ("as", .keyword .asKw),
  ("let", .keyword .letKw),
  ("data", .keyword .dataKw),
  ("class", .keyword .classKw),
  ("forall", .keyword .forallKw),
  ("instance", .keyword .instanceKw),
  ("if", .keyword .ifKw),
  ("else", .keyword .elseKw),
  ("for", .keyword .forKw),
  ("switch", .keyword .switchKw),
  ("type", .keyword .typeKw),
  ("case", .keyword .caseKw),
  ("default", .keyword .defaultKw),
  ("match", .keyword .matchKw),
  ("public", .keyword .publicKw),
  ("payable", .keyword .payableKw),
  ("function", .keyword .functionKw),
  ("constructor", .keyword .constructorKw),
  ("fallback", .keyword .fallbackKw),
  ("return", .keyword .returnKw),
  ("leave", .keyword .leaveKw),
  ("continue", .keyword .continueKw),
  ("break", .keyword .breakKw),
  ("lam", .keyword .lamKw),
  ("assembly", .keyword .assemblyKw),
  ("pragma", .keyword .pragmaKw),
  ("true", .keyword .trueKw),
  ("false", .keyword .falseKw)
]

private def contextualCases : List String := [
  "comptime", "derive", "enum", "from", "hiding", "impl",
  "mapping", "returns", "trait", "where", "while"
]

private def symbolCases : List (String × TokenKind) := [
  (":=", .symbol .colonEqual),
  ("->", .symbol .arrow),
  ("=>", .symbol .fatArrow),
  ("==", .symbol .equalEqual),
  ("!=", .symbol .notEqual),
  (">=", .symbol .greaterEqual),
  ("<=", .symbol .lessEqual),
  ("&&", .symbol .logicalAnd),
  ("||", .symbol .logicalOr),
  ("+=", .symbol .plusEqual),
  ("-=", .symbol .minusEqual),
  ("*=", .symbol .starEqual),
  ("/=", .symbol .slashEqual),
  ("^=", .symbol .caretEqual),
  ("&=", .symbol .ampEqual),
  ("|=", .symbol .pipeEqual),
  ("%=", .symbol .percentEqual),
  ("~=", .symbol .tildeEqual),
  ("+", .symbol .plus),
  ("-", .symbol .minus),
  ("*", .symbol .star),
  ("/", .symbol .slash),
  ("%", .symbol .percent),
  ("!", .symbol .bang),
  ("~", .symbol .tilde),
  ("<", .symbol .less),
  (">", .symbol .greater),
  ("=", .symbol .equal),
  ("|", .symbol .pipe),
  ("&", .symbol .amp),
  ("^", .symbol .caret),
  ("@", .symbol .at),
  ("?", .symbol .question),
  ("#", .symbol .hash),
  (".", .symbol .dot),
  (":", .symbol .colon),
  (";", .symbol .semicolon),
  (",", .symbol .comma),
  ("(", .symbol .leftParen),
  (")", .symbol .rightParen),
  ("{", .symbol .leftBrace),
  ("}", .symbol .rightBrace),
  ("[", .symbol .leftBracket),
  ("]", .symbol .rightBracket),
  ("_", .symbol .underscore)
]

/-- Run exact recognition and span checks for every closed lexer catalog item. -/
def testSyntaxLexerCatalog : IO Unit := do
  for (spelling, expected) in keywordCases do
    expectSingle spelling expected
  for spelling in contextualCases do
    expectSingle spelling (.identifier spelling)
  for (spelling, expected) in symbolCases do
    expectSingle spelling expected

end Tests
