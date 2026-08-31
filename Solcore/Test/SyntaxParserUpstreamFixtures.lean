import Solcore.Syntax.Parser

/-!
Pinned positive parser fixtures from `solcore-rs` commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`.

The sources are embedded so this regression does not depend on an external
checkout at test time.
-/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def fixture (name : String) (lines : List String) : String × String :=
  (name, String.intercalate "\n" lines ++ "\n")

private def upstreamOkFixtures : List (String × String) := [
  fixture "body_return_min.sol" [
    "function main() returns (word) {",
    "  return 1;",
    "}"
  ],
  fixture "comptime_match_label.sol" [
    "function classify(x: word) returns (word) {",
    "  match (x) {",
    "case comptime 1 {",
    "return 1;",
    "}",
    "default {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "comptime_modifier.sol" [
    "type comptime = word;",
    "",
    "contract ComptimeModifier {",
    "  function f(comptime x: word) returns (comptime<word>) {",
    "    return x;",
    "  }",
    "",
    "  function identifier(x: comptime) returns (comptime) {",
    "    let comptime : word = 1;",
    "    let y : comptime<word> = f(comptime);",
    "    return y;",
    "  }",
    "}"
  ],
  fixture "contract_modifiers_constructor_fallback.sol" [
    "contract Modifiers {",
    "  constructor() {}",
    "",
    "  function ping() public {}",
    "",
    "  function deposit() public payable returns (uint256) {",
    "    return 0;",
    "  }",
    "",
    "  fallback() payable {}",
    "}"
  ],
  fixture "dot_ctor_expr_pattern.sol" [
    "enum Option { None, Some(word) }",
    "",
    "function mkSome(x: word) returns (Option) {",
    "  return .Some(x);",
    "}",
    "",
    "function fromOption(x: Option) returns (word) {",
    "  match (x) {",
    "case .Some(v) {",
    "return v;",
    "}",
    "case .None {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "export_operator_list.sol" [
    "export { f, (^^) };"
  ],
  fixture "expression_bodied.sol" [
    "function zero() returns (word) {",
    "  0",
    "}",
    "",
    "function apply<a, b>(f: function(a) returns (b), x: a) returns (b) {",
    "  f(x)",
    "}",
    "",
    "function choose<a>(c: bool, a: a, b: a) returns (a) {",
    "   c  ?  a  :  b",
    "}",
    "",
    "function keepThen(then: word) returns (word) {",
    "  then",
    "}"
  ],
  fixture "for_loop.sol" [
    "function sum10() returns (word) {",
    "  let s : word = 0;",
    "  for (let i = 1; i <= 10; i = i + 1) {",
    "    s = s + i;",
    "  }",
    "  return s;",
    "}"
  ],
  fixture "import_alias_operator_hiding.sol" [
    "import {A as B, (^^)} from mod hiding {C};"
  ],
  fixture "import_external_alias.sol" [
    "import * as X from @lib.a.b;"
  ],
  fixture "import_mixed_wildcard.sol" [
    "import * from glob;",
    "import * from glob2;",
    "import * from glob3;"
  ],
  fixture "import_wildcard_selector.sol" [
    "import * from mod;"
  ],
  fixture "match_arm_block.sol" [
    "function main(foo: (word, word)) returns (word) {",
    "  let res: word;",
    "  match (foo) {",
    "case (v0, v1) {",
    "{",
    "    let x: word = v1;",
    "    res = x;",
    "  }",
    "}",
    "}",
    "  return res;",
    "}"
  ],
  fixture "match_trailing_semicolon.sol" [
    "function f() {",
    "  match (0) {",
    "default {",
    "return ();",
    "}",
    "}",
    "}"
  ],
  fixture "no_diagnostics.sol" [
    "function ok() {}"
  ],
  fixture "operators_compound_assign.sol" [
    "function operators(x: word, y: word, z: word) returns (word) {",
    "  let acc = x % y;",
    "  acc = (acc & y) | (x ^ z);",
    "  acc += x;",
    "  acc -= y;",
    "  acc ^= z;",
    "  acc &= x;",
    "  acc |= y;",
    "  acc %= z;",
    "  return acc;",
    "}"
  ],
  fixture "parser_catchup_h.sol" [
    "enum First { First(word) }",
    "enum Second { Second }",
    "",
    "export mod;",
    "export mod as M;",
    "export mod.{a};",
    "export { T(*) };",
    "",
    "import {T} from m;"
  ],
  fixture "proxy_expression.sol" [
    "function main(x: word) returns (word) {",
    "  let p = @word;",
    "  let pairProxy = @(word, word);",
    "  let annotated = p ;",
    "  return x;",
    "}"
  ],
  fixture "proxy_type_sugar.sol" [
    "function proxy_sig(x: @word) returns (@word) {}"
  ],
  fixture "qualified_constructor_pattern_3_segment.sol" [
    "function main(x: mod.Type.Bool) returns (word) {",
    "  match (x) {",
    "case mod.Type.True {",
    "return 1;",
    "}",
    "default {",
    "return 0;",
    "}",
    "}",
    "}"
  ],
  fixture "qualified_constructor_patterns.sol" [
    "contract QualifiedConstructorPatterns {",
    "  enum Option<a> { None, Some(a) }",
    "",
    "  function join<a>(mmx: Option<Option<a>>) returns (Option<a>) {",
    "    match (mmx) {",
    "case Option.None {",
    "return Option.None;",
    "}",
    "case Option.Some(Option.Some(x)) {",
    "return Option.Some(x);",
    "}",
    "case Option.Some(Option.None) {",
    "return Option.None;",
    "}",
    "}",
    "  }",
    "}"
  ],
  fixture "qualified_type_return.sol" [
    "function qualified_ret() returns (mod.Type) {}"
  ],
  fixture "tuple_unit_sail.sol" [
    "enum Pair<a, b> { Pair(a, b) }",
    "",
    "function fst<a, b>(p: (a, b)) returns (a) {",
    "  match (p) {",
    "case (x, y) {",
    "return x;",
    "}",
    "}",
    "}",
    "",
    "function tupleValue() returns (word, word) {",
    "  return (1, 0);",
    "}",
    "",
    "function unitValue() {",
    "  return ();",
    "}",
    "",
    "function nestedTupleUnitPattern(p: ((), (word, word))) returns (word) {",
    "  match (p) {",
    "case ((), (x, y)) {",
    "return x;",
    "}",
    "}",
    "}",
    "",
    "function groupedSinglePattern(p: word) returns (word) {",
    "  match (p) {",
    "case (y) {",
    "return y;",
    "}",
    "}",
    "}",
    "",
    "function pairData(x: word, y: word) returns (Pair<word, word>) {",
    "  return Pair(x, y);",
    "}"
  ]
]

private def hasRecoveryItem : TopItem → Bool
  | { value := .error, .. } => true
  | { value := .contract declaration, .. } =>
      declaration.value.members.any fun member => member.value == .error
  | _ => false

private def checkFixture (name content : String) : IO Unit := do
  let file : SourceFile := {
    id := { origin := .main, path := s!"upstream-ok/{name}" }
    content
  }
  let output ← match Parser.parse file with
    | .ok output => pure output
    | .error error => throw (IO.userError
        s!"{name}: parser invariant failed: {reprStr error}")
  unless output.lexicalDiagnostics.isEmpty do
    throw (IO.userError
      s!"{name}: lexical diagnostics: {reprStr output.lexicalDiagnostics}")
  unless output.parseDiagnostics.isEmpty do
    throw (IO.userError
      s!"{name}: parse diagnostics: {reprStr output.parseDiagnostics}")
  unless output.parsed.span.isValidFor file &&
      output.parsed.items.all (fun item => item.span.isValidFor file) do
    throw (IO.userError s!"{name}: invalid parsed span")
  if output.parsed.items.any hasRecoveryItem then
    throw (IO.userError s!"{name}: retained a declaration recovery node")

def testSyntaxParserUpstreamFixtures : IO Unit := do
  unless upstreamOkFixtures.length == 23 do
    throw (IO.userError "pinned upstream fixture catalog must contain 23 files")
  for (name, content) in upstreamOkFixtures do
    checkFixture name content

end Tests
