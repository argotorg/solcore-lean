import Solcore.Syntax.Parser.Term

/-! Direct executable regressions for canonical expressions and patterns. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat
private def termSource : SourceId := {
  origin := .main
  path := "parser-terms.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private def initialState (label content : String) : IO Parser.State := do
  let file : SourceFile := { id := termSource, content }
  match Lexer.lex file with
  | .error error => throw (IO.userError
      s!"{label}: lexer invariant failed: {reprStr error}")
  | .ok lexed =>
      assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
      pure (Parser.State.initial file lexed)

private structure ExpressionRun where
  value : Expr
  state : Parser.State

private structure PatternRun where
  value : Pattern
  state : Parser.State

private def runExpression (label content : String)
    (complete : Bool := true) : IO ExpressionRun := do
  let state ← initialState label content
  match Parser.expression state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: expression left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: expression rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: expression invariant: {reprStr error}")

private def runPattern (label content : String)
    (complete : Bool := true) : IO PatternRun := do
  let state ← initialState label content
  match Parser.pattern state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: pattern left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: pattern rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: pattern invariant: {reprStr error}")

private inductive ExpressionShape where
  | literal (value : CoreLiteralValue)
  | identifier (name : String)
  | dotConstructor (name : String)
      (arguments : Option (List ExpressionShape))
  | unary (operator : UnaryOp) (operand : ExpressionShape)
  | binary (left : ExpressionShape) (operator : BinaryOp)
      (right : ExpressionShape)
  | index (base index : ExpressionShape)
  | call (callee : ExpressionShape) (arguments : List ExpressionShape)
  | field (base : ExpressionShape) (name : String)
  | conditional (condition thenBranch elseBranch : ExpressionShape)
  | group (inner : ExpressionShape)
  | tuple (elements : List ExpressionShape)
  | array (elements : List ExpressionShape)
  | error
  | other
  deriving Repr, BEq, Inhabited

private partial def expressionShape (expression : Expr) : ExpressionShape :=
  match expression.value with
  | .literal literal => .literal literal.value
  | .identifier name => .identifier name.value
  | .dotConstructor _ name arguments => .dotConstructor name.value
      (arguments.map fun values => values.elements.map expressionShape)
  | .unary operator operand => .unary operator.value (expressionShape operand)
  | .binary left operator right =>
      .binary (expressionShape left) operator.value (expressionShape right)
  | .index base _ index => .index (expressionShape base) (expressionShape index)
  | .call callee arguments => .call (expressionShape callee)
      (arguments.elements.map expressionShape)
  | .field base _ name => .field (expressionShape base) name.value
  | .conditional condition _ thenBranch _ elseBranch =>
      .conditional (expressionShape condition) (expressionShape thenBranch)
        (expressionShape elseBranch)
  | .group inner => .group (expressionShape inner)
  | .tuple values => .tuple (values.elements.map expressionShape)
  | .array values => .array (values.elements.map expressionShape)
  | .error => .error
  | _ => .other

private inductive PatternShape where
  | wildcard
  | literal (value : CoreLiteralValue)
  | binder (name : String)
  | constructor (leadingDot : Bool) (qualifiers : List String)
      (name : String) (arguments : Option (List PatternShape))
  | comptime (expression : ExpressionShape)
  | group (inner : PatternShape)
  | tuple (elements : List PatternShape)
  | error
  deriving Repr, BEq, Inhabited

private partial def patternShape (pattern : Pattern) : PatternShape :=
  match pattern.value with
  | .wildcard _ => .wildcard
  | .literal literal => .literal literal.value
  | .binder name => .binder name.value
  | .constructor dot qualifiers name arguments => .constructor dot.isSome
      (qualifiers.map (fun item => item.value)) name.value
      (arguments.map fun values => values.elements.toList.map patternShape)
  | .comptime _ expression => .comptime (expressionShape expression)
  | .group inner => .group (patternShape inner)
  | .tuple values => .tuple (values.elements.map patternShape)
  | .error => .error

private def ident (name : String) : ExpressionShape := .identifier name
private def bin (left : ExpressionShape) (op : BinaryOp)
    (right : ExpressionShape) : ExpressionShape := .binary left op right

private def testAtomsAndTuples : IO Unit := do
  for (source, expected) in [
      ("(x)", .group (ident "x")),
      ("(x,)", .group (ident "x")),
      ("()", .tuple []),
      ("(x, y,)", .tuple [ident "x", ident "y"]),
      (".C", .dotConstructor "C" none),
      (".C()", .dotConstructor "C" (some [])),
      ("[x, y]", .array [ident "x", ident "y"])
    ] do
    let run ← runExpression s!"atom {source}" source
    assertEqual (expressionShape run.value) expected s!"atom shape {source}"
    assertEqual (byteRange run.value.span) (0, source.utf8ByteSize)
      s!"atom span {source}"

private def testSourcePreservingWitnesses : IO Unit := do
  let proxy ← runExpression "proxy expression" "@pkg.Box<word>"
  assertEqual proxy.state.diagnostics [] "proxy expression diagnostics"
  assertEqual (byteRange proxy.value.span) (0, 14) "proxy expression span"
  match proxy.value.value with
  | .proxy marker type =>
      assertEqual (byteRange marker) (0, 1) "proxy marker span"
      assertEqual (byteRange type.span) (1, 14) "proxied type span"
      match type.value with
      | .named name (some arguments) =>
          assertEqual
            (name.value.components.toList.map (fun item => item.value))
            ["pkg", "Box"] "proxied qualified name"
          assertEqual (byteRange name.span) (1, 8) "proxied name span"
          assertEqual (byteRange arguments.span) (8, 14)
            "proxied type arguments span"
          match arguments.elements.toList with
          | [{ span, value := .named argumentName none }] =>
              assertEqual (byteRange span) (9, 13)
                "proxied argument span"
              assertEqual
                (argumentName.value.components.toList.map
                  (fun item => item.value))
                ["word"] "proxied argument name"
          | values => throw (IO.userError
              s!"proxied type arguments changed: {reprStr values}")
      | value => throw (IO.userError
          s!"proxied type changed: {reprStr value}")
  | value => throw (IO.userError
      s!"proxy expression was not preserved: {reprStr value}")

  let lambdaSource :=
    "lam(x, comptime y, comptime z: word) { return z; }"
  let lambda ← runExpression "lambda parameter distinctions" lambdaSource
  assertEqual (byteRange lambda.value.span) (0, lambdaSource.utf8ByteSize)
    "lambda expression span"
  assertEqual (lambda.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((7, 17), .constraintViolation .comptimeParameterRequiresType)
  ] "untyped comptime lambda diagnostic"
  match lambda.value.value with
  | .lambda keyword parameters none body =>
      assertEqual (byteRange keyword) (0, 3) "lambda keyword span"
      assertEqual (byteRange parameters.span) (3, 36)
        "lambda parameter-list span"
      match parameters.elements with
      | [
          { span := inferredSpan, value := .inferred inferredName },
          { span := errorSpan, value := .error },
          { span := typedSpan,
            value := .typed (some comptimeSpan) typedName typedType }
        ] =>
          assertEqual (byteRange inferredSpan) (4, 5)
            "inferred lambda parameter span"
          assertEqual inferredName.value "x" "inferred lambda parameter"
          assertEqual (byteRange errorSpan) (7, 17)
            "untyped comptime error placeholder span"
          assertEqual (byteRange typedSpan) (19, 35)
            "typed comptime parameter span"
          assertEqual (byteRange comptimeSpan) (19, 27)
            "typed comptime marker span"
          assertEqual typedName.value "z" "typed comptime parameter"
          match typedType.value with
          | .named typeName none =>
              assertEqual
                (typeName.value.components.toList.map
                  (fun item => item.value))
                ["word"] "typed comptime parameter type"
          | value => throw (IO.userError
              s!"typed comptime parameter type changed: {reprStr value}")
      | values => throw (IO.userError
          s!"lambda parameter distinctions changed: {reprStr values}")
      match body.value with
      | [{ value := .returnStmt (some returned), .. }] =>
          assertEqual (expressionShape returned) (ident "z")
            "lambda body preserved after parameter error"
      | statements => throw (IO.userError
          s!"lambda body changed after parameter error: {reprStr statements}")
  | value => throw (IO.userError
      s!"lambda expression changed: {reprStr value}")

private def testTrailingCommaRejection : IO Unit := do
  for (source, close) in [("[x,]", Symbol.rightBracket),
      ("f(x,)", .rightParen), (".C(x,)", .rightParen)] do
    let state ← initialState s!"trailing comma {source}" source
    match Parser.expression state with
    | .reject failure _ =>
        assertEqual failure.found (some (.symbol close))
          s!"trailing comma closing token {source}"
        assertEqual failure.expected { head := .expression, tail := [] }
          s!"trailing comma expectation {source}"
    | .ok { value := .error, .. } next =>
        if next.atEnd then
          throw (IO.userError s!"trailing comma fully consumed in {source}")
        match next.diagnostics with
        | { kind := .unexpected (some (.symbol found)) _ .expression, .. } :: _ =>
            assertEqual found close s!"recovered trailing comma {source}"
        | diagnostics => throw (IO.userError
            s!"trailing comma recovery changed in {source}: {reprStr diagnostics}")
    | result => throw (IO.userError
        s!"trailing comma accepted in {source}: {reprStr result}")

private def testPostfixAndUnary : IO Unit := do
  let postfixRun ← runExpression "postfix fold" "base[i](x).field[j]"
  assertEqual (expressionShape postfixRun.value)
    (.index (.field (.call (.index (ident "base") (ident "i"))
      [ident "x"]) "field") (ident "j")) "postfix left fold"
  assertEqual (byteRange postfixRun.value.span) (0, 19) "postfix full span"
  match postfixRun.value.value with
  | .index field outerBrackets _ =>
      assertEqual (byteRange outerBrackets) (16, 19) "outer index span"
      match field.value with
      | .field call dot name =>
          assertEqual (byteRange field.span) (0, 16) "field span"
          assertEqual (byteRange dot) (10, 11) "field dot span"
          assertEqual (byteRange name.span) (11, 16) "field name span"
          assertEqual (byteRange call.span) (0, 10) "call span"
      | _ => throw (IO.userError "postfix field shape changed")
  | _ => throw (IO.userError "postfix outer index changed")

  let unary ← runExpression "unary fold" "!~!x"
  assertEqual (expressionShape unary.value)
    (.unary .logicalNot (.unary .bitNot
      (.unary .logicalNot (ident "x")))) "unary right fold"
  assertEqual (byteRange unary.value.span) (0, 4) "unary span"

private def testPrecedenceAndAssociativity : IO Unit := do
  let source := "a || b && c == d < e | f ^ g & h + i * j"
  let run ← runExpression "all precedence" source
  assertEqual (expressionShape run.value)
    (bin (ident "a") .logicalOr
      (bin (ident "b") .logicalAnd
        (bin (ident "c") .equal
          (bin (ident "d") .less
            (bin (ident "e") .bitOr
              (bin (ident "f") .bitXor
                (bin (ident "g") .bitAnd
                  (bin (ident "h") .add
                    (bin (ident "i") .multiply (ident "j"))))))))))
    "all precedence levels"
  let left ← runExpression "left associativity" "a - b - c"
  assertEqual (expressionShape left.value)
    (bin (bin (ident "a") .subtract (ident "b"))
      .subtract (ident "c")) "left associativity"
  for (source, operator) in [("a < b < c", BinaryOp.less),
      ("a == b == c", .equal)] do
    let prefixRun ← runExpression s!"nonassociative {source}" source false
    assertEqual (expressionShape prefixRun.value)
      (bin (ident "a") operator (ident "b")) s!"nonassociative prefix {source}"
    assertEqual prefixRun.state.remainingCount 2 s!"nonassociative remainder {source}"

private def testConditionals : IO Unit := do
  let right ← runExpression "right conditional" "a ? b : c ? d : e"
  assertEqual (expressionShape right.value)
    (.conditional (ident "a") (ident "b")
      (.conditional (ident "c") (ident "d") (ident "e")))
    "right-associative conditional"
  let nested ← runExpression "nested then" "a ? b ? c : d : e"
  assertEqual (expressionShape nested.value)
    (.conditional (ident "a")
      (.conditional (ident "b") (ident "c") (ident "d")) (ident "e"))
    "nested then conditional"

private def testExpressionRecovery : IO Unit := do
  let run ← runExpression "atom recovery" "+ -," false
  assertEqual (expressionShape run.value) .error "atom recovery node"
  assertEqual (byteRange run.value.span) (0, 3) "atom recovery span"
  assertEqual run.state.peekKind? (some (.symbol .comma)) "atom recovery boundary"
  assertEqual (run.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((0, 1), .unexpected (some (.symbol .plus))
      { head := .expression, tail := [] } .expression),
    ((0, 3), .recovered .expressionAtom)
  ] "atom recovery diagnostics"

private def testPatternForms : IO Unit := do
  for (source, expected) in [
      ("_", PatternShape.wildcard),
      ("42", .literal (.decimal "42")),
      ("true", .binder "true"),
      ("λvalue", .binder "λvalue"),
      ("Value", .constructor false [] "Value" none),
      (".C", .constructor true [] "C" none),
      (".C(x)", .constructor true [] "C" (some [.binder "x"])),
      ("(x)", .group (.binder "x")),
      ("()", .tuple []),
      ("(x, _,)", .tuple [.binder "x", .wildcard])
    ] do
    let run ← runPattern s!"pattern {source}" source
    assertEqual (patternShape run.value) expected s!"pattern shape {source}"

  let qualified ← runPattern "qualified constructor"
    "pkg.Option.Some(x, _)"
  assertEqual (patternShape qualified.value)
    (.constructor false ["pkg", "Option"] "Some"
      (some [.binder "x", .wildcard])) "qualified constructor shape"
  assertEqual (byteRange qualified.value.span) (0, 21) "constructor span"
  match qualified.value.value with
  | .constructor _ _ _ (some arguments) =>
      assertEqual (byteRange arguments.span) (15, 21) "constructor args span"
  | _ => throw (IO.userError "qualified constructor arguments changed")

  let comptime ← runPattern "comptime pattern" "comptime x + 1"
  assertEqual (patternShape comptime.value)
    (.comptime (bin (ident "x") .add (.literal (.decimal "1"))))
    "comptime expression pattern"
  assertEqual (byteRange comptime.value.span) (0, 14) "comptime pattern span"

private def testPatternRecovery : IO Unit := do
  let run ← runPattern "pattern recovery" "+ - =>" false
  assertEqual (patternShape run.value) .error "pattern recovery node"
  assertEqual (byteRange run.value.span) (0, 3) "pattern recovery span"
  assertEqual run.state.peekKind? (some (.symbol .fatArrow))
    "pattern recovery boundary"
  assertEqual (run.state.diagnostics.map fun item => item.kind) [
    .unexpected (some (.symbol .plus))
      { head := .pattern, tail := [] } .pattern,
    .recovered .pattern
  ] "pattern recovery diagnostics"

/-- Run direct expression and pattern parser regressions. -/
def testSyntaxParserTerms : IO Unit := do
  testAtomsAndTuples
  testSourcePreservingWitnesses
  testTrailingCommaRejection
  testPostfixAndUnary
  testPrecedenceAndAssociativity
  testConditionals
  testExpressionRecovery
  testPatternForms
  testPatternRecovery

end Tests
