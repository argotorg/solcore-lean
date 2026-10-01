import Solcore.Test.SourceCompilerFeatureSupport

set_option autoImplicit false
namespace Tests.SourceCompilerIntegers
open Solcore Solcore.Frontend Tests.SourceCompilerFeatureSupport

private def operations : List (String × String × Bool) := [
  ("add", "+", false), ("sub", "-", false), ("mul", "*", false),
  ("div", "/", false), ("mod", "%", false),
  ("and", "&", false), ("or", "|", false), ("xor", "^", false),
  ("eq", "==", true), ("ne", "!=", true), ("lt", "<", true),
  ("le", "<=", true), ("gt", ">", true), ("ge", ">=", true)
]

private def workspaceText : String := String.intercalate "\n"
    ((operations.flatMap fun (name, operator, comparison) => [0, 5].map fun (right : Nat) =>
      "function op" ++ name ++ toString right ++ "(" ++ (if comparison then "comptime " else "") ++
        "left: integer) returns (" ++ (if comparison then "Bool" else "integer") ++
        ") { return left " ++ operator ++ " " ++ toString right ++ "; }") ++ [
      "function negate() returns (integer) { return ~5; }",
      "function callBuiltin(left: integer, right: integer) returns (integer) { return integerAdd(left, right); }",
      "function builtinValue(left: integer, right: integer) returns (integer) { let f: function(integer, integer) returns (integer) = integerSub; return f(left, right); }",
      "function intoWord(comptime left: integer) returns (Word) { return wordFromInteger(left); }",
      "function intoInteger(left: Word) returns (integer) { return wordToInteger(left); }",
      "function nativeLiteral() returns (integer) { return 1234567890123456789012345678901234567890; }",
      "function order(value: integer) returns (integer) {",
      " let step: function(integer) returns (integer) = lam(delta: integer) -> integer { value = integerAdd(value, delta); return value; };",
      " return integerSub(step(1), step(2)); }",
      "function recurse(value: integer) returns (integer) { return value == 0 ? 7 : recurse(value - 1); }",
      "function absent() returns (integer) { let value: integer; return value; }"
    ])

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := workspaceText }]
}


private def compile (program : CheckedProgram) (name : String) : IO Entry :=
  compileNamed program name [] {options with compilationFuel := 8192}
private def expect (entry : Entry) (arguments : List Value) (expected : Value) : IO Unit := do
  for _ in [0, 1] do
    require ((← entry.run arguments) == expected) "Integer result or cached entry reuse changed"

private def arithmetic (name : String) (left right : Int) : Value :=
  match name with
  | "add" => .integer (left + right)
  | "sub" => .integer (left - right)
  | "mul" => .integer (left * right)
  | "div" => .integer (Core.Integer.divide left right)
  | "mod" => .integer (Core.Integer.modulo left right)
  | "and" => .integer (Core.Integer.bitAnd left right)
  | "or" => .integer (Core.Integer.bitOr left right)
  | "xor" => .integer (Core.Integer.bitXor left right)
  | "eq" => .bool (left == right)
  | "ne" => .bool (left != right)
  | "lt" => .bool (left < right)
  | "le" => .bool (left ≤ right)
  | "gt" => .bool (left > right)
  | _ => .bool (left ≥ right)

def run : IO Unit := do
  let program ← get "Integer checking" (checkProgram workspace)
  let large : Int := Int.ofNat (2 ^ 300 + 19)
  for (name, _, _) in operations do
    for (right : Nat) in [0, 5] do
      let entry ← compile program ("op" ++ name ++ toString right)
      for left in [large, -17, 0] do
        expect entry [.integer left] (arithmetic name left (Int.ofNat right))
  expect (← compile program "negate") [] (.integer (~~~(5 : Int)))
  expect (← compile program "callBuiltin") [.integer large, .integer (-3)] (.integer (large - 3))
  expect (← compile program "builtinValue") [.integer large, .integer (-3)] (.integer (large + 3))
  expect (← compile program "intoWord") [.integer (-1)] (.word Core.Word.maximum)
  expect (← compile program "intoInteger") [.word Core.Word.maximum] (.integer (Int.ofNat Core.Word.maximum.val))
  expect (← compile program "nativeLiteral") [] (.integer 1234567890123456789012345678901234567890)
  let order ← compile program "order"
  expect order [.integer large] (.integer (-2))
  order.checkResume [.integer large] (.integer (-2))
  expect (← compile program "recurse") [.integer 8] (.integer 7)
  let absent ← compile program "absent"
  let invocation ← absent.invoke []
  match invocation.outcome with
  | .failed reason _ => require ((← invocation.diagnostic reason).isSome) "Integer absence lost source diagnostic"
  | _ => throw (IO.userError "Integer absence did not fail")
  IO.println "public source Integer Core execution GREEN"
end Tests.SourceCompilerIntegers
