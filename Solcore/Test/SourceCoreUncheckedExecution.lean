import Solcore.Frontend.SourceCoreExecution

/-! `unchecked { … }` blocks through the public source API (solcore-rs #119),
as far as Lean implements them: `+`, `-` and `*` and their compound forms on
Words, which wrap in a block as outside it, `unchecked` as an ordinary name,
blocks in loops, lambdas written in a block, helpers called from one, and the
rejected programs. Upstream's unchecked `/` and `%` panic on a zero divisor;
Lean has no panics yet, so a block rejects them while the file loads.
Every expected value is what the pinned Rust paths give (lane D's probe, in
`docs/design/integer-types-unchecked-shifts.md`). -/
set_option autoImplicit false
namespace Tests.SourceCoreUncheckedExecution
open Solcore Solcore.Frontend SourceCoreExecution

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Value := .word (Core.Word.ofNatModulo n)
private def workspaceOf (lines : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" lines}] }

private def maximum : Nat := 2 ^ 256 - 1
private def high : Nat := 2 ^ 255

private def workspace : Workspace.RawWorkspace := workspaceOf [
  "function wrapAdd(x: Word) returns (Word) { unchecked { return x + 1; } }",
  "function wrapSub(x: Word) returns (Word) { let r: Word = 0; unchecked { r = r - x; } return r; }",
  "function wrapMul(x: Word, y: Word) returns (Word) { unchecked { let r: Word = x * y; return r; } }",
  "function compound(x: Word) returns (Word) { let r: Word = x; unchecked { r += 1; r *= 3; r -= 2; } return r; }",
  "function named() returns (Word) { let unchecked: Word = 4; unchecked = unchecked + 1; return unchecked; }",
  "function loop(n: Word) returns (Word) { let total: Word = 0; let i: Word = 0; while (i < n) { unchecked { total = total + i; i = i + 1; } } return total; }",
  "function lambdaDivision(a: Word, b: Word) returns (Word) { unchecked { let divide = lam(x: Word, y: Word) -> Word { return x / y; }; return divide(a, b); } }",
  "function helper(a: Word, b: Word) returns (Word) { return a / b; }",
  "function helperDivision(a: Word, b: Word) returns (Word) { unchecked { return helper(a, b); } }",
  "function lambdaBlock(x: Word) returns (Word) { unchecked { let next = lam(y: Word) -> Word { unchecked { return y + 1; } }; return next(x) * 2; } }",
  "function shadowed(x: Word) returns (Word) { let r: Word = x; unchecked { let r: Word = 7; r = r + 1; } return r; }"
]

private def names : List String :=
  ["wrapAdd", "wrapSub", "wrapMul", "compound", "named", "loop", "lambdaDivision",
    "helperDivision", "lambdaBlock", "shadowed"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"unchecked fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"unchecked export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"unchecked language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "unchecked execution exhausted")
  | .error error => throw (IO.userError s!"unchecked invocation: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"unchecked bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "unchecked bootstrap exhausted")

private def rejected (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error _ => pure ()

/-- The block's own load error, so that a division is not rejected for an
unrelated reason. -/
private def rejectedWhileLoading (label : String) (expected : Syntax.Unchecked.Error → Bool)
    (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.loading (.uncheckedBlock _ error)] =>
      unless expected error do throw (IO.userError s!"{label} gave {reprStr error}")
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

/-- Inference itself rejects the program, after loading succeeded. -/
private def rejectedByInference (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error [.inference _] => pure ()
  | .error errors => throw (IO.userError s!"{label} gave {reprStr errors}")

def run : IO Unit := do
  let program ← get "unchecked check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "unchecked compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "unchecked root missing")
  let mut session ← boot (← compiled.open)
  let cases : List (Nat × List Nat × Nat) :=
    [(0, [5], 6), (0, [maximum], 0),
      (1, [1], maximum), (1, [0], 0),
      (2, [high, 2], 0), (2, [3, 5], 15),
      (3, [maximum], maximum - 1), (3, [4], 13),
      (4, [], 5),
      (5, [4], 6), (5, [0], 0),
      (6, [7, 2], 3), (6, [7, 0], 0),
      (7, [9, 0], 0), (7, [9, 4], 2),
      (8, [maximum], 0), (8, [4], 10),
      (9, [3], 3)]
  for (index, arguments, expected) in cases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == word expected)
      s!"unchecked case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  rejectedWhileLoading "a block in a block" (fun | .nested _ => true | _ => false)
    ["function bad() returns (Word) { unchecked { unchecked { return 1; } } }"]
  rejectedWhileLoading "a division in a block" (fun | .division _ => true | _ => false)
    ["function bad(a: Word, b: Word) returns (Word) { unchecked { return a / b; } }"]
  rejectedWhileLoading "a remainder in a block" (fun | .division _ => true | _ => false)
    ["function bad(a: Word, b: Word) returns (Word) { unchecked { return a % b; } }"]
  rejectedWhileLoading "a compound remainder in a block" (fun | .division _ => true | _ => false)
    ["function bad(a: Word, b: Word) returns (Word) { unchecked { a %= b; } return a; }"]
  discard <| get "checked integer arithmetic"
    (checkProgram (workspaceOf ["function good(n: integer) returns (integer) { return n + 1; }"]))
  rejectedByInference "unchecked arithmetic on integer"
    ["function bad(n: integer) returns (integer) { unchecked { return n + 1; } }"]
  rejected "a block as an expression"
    ["function bad() returns (Word) { let x: Word = unchecked { 1 }; return x; }"]
  IO.println "SOURCE_CORE_UNCHECKED_PASS: unchecked `+`, `-` and `*` wrap on Words with their compound forms, `unchecked` stays a name, blocks reach no lambda body or helper, and nested blocks, unchecked `/` and `%`, unchecked `integer` arithmetic and blocks as expressions are rejected"

end Tests.SourceCoreUncheckedExecution
