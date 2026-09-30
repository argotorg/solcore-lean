import Solcore.Frontend.SourceCompiler

set_option autoImplicit false

namespace Tests.SourceCompilerIntegers

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

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

private def compile (program : CheckedProgram) (name : String) (preference : SourceCompiler.BackendPreference) :
    IO SourceCompiler.CompiledEntry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"missing function {name}")
  match SourceCompiler.compileChecked program (.declaration signature.id [])
    { backendPreference := preference, stagingFuel := 8192 } with
  | .ok entry =>
      assertTrue (entry.backend == .core) s!"{name} failed Core migration"
      pure entry
  | .error error => throw (IO.userError s!"{name} compilation failed {reprStr error}")

private def expect (entry : SourceCompiler.CompiledEntry) (arguments : List Core.Value)
    (expected : Core.Value) : IO Unit := do
  for _ in [0, 1] do
    match entry.runCore arguments { executionFuel := 32768 } with
    | .ok (.coreLanguageResult (.succeeded actual _)) =>
        assertTrue (actual == expected) s!"Integer result changed: {reprStr actual}"
    | result => throw (IO.userError s!"Integer execution failed {reprStr result}")

private def arithmetic (name : String) (left right : Int) : Core.Value :=
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
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"Integer workspace rejected {reprStr error}")
  let large : Int := Int.ofNat (2 ^ 300 + 19)
  for preference in [SourceCompiler.BackendPreference.automatic, .core] do
    for (name, _, _) in operations do
      for (right : Nat) in [0, 5] do
        let entry ← compile program ("op" ++ name ++ toString right) preference
        for left in [large, -17, 0] do
          expect entry [.integer left] (arithmetic name left (Int.ofNat right))
    expect (← compile program "negate" preference) [] (.integer (~~~(5 : Int)))
    expect (← compile program "callBuiltin" preference) [.integer large, .integer (-3)] (.integer (large - 3))
    expect (← compile program "builtinValue" preference) [.integer large, .integer (-3)] (.integer (large + 3))
    expect (← compile program "intoWord" preference) [.integer (-1)] (.word Core.Word.maximum)
    expect (← compile program "intoInteger" preference) [.word Core.Word.maximum]
      (.integer (Int.ofNat Core.Word.maximum.val))
    expect (← compile program "nativeLiteral" preference) []
      (.integer 1234567890123456789012345678901234567890)
    expect (← compile program "order" preference) [.integer large]
      (.integer (-2))
    expect (← compile program "recurse" preference) [.integer 8] (.integer 7)
    let absent ← compile program "absent" preference
    match absent.runCore [] { executionFuel := 32768 } with
    | .ok (.coreLanguageResult (.failed reason _)) =>
        assertTrue (absent.coreFailureDiagnostic? reason |>.isSome) "Integer absence lost its source diagnostic"
    | result => throw (IO.userError s!"Integer absence changed {reprStr result}")
  IO.println "public source Integer Core execution GREEN"

end Tests.SourceCompilerIntegers
