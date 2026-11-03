import Solcore.Frontend.SourceCoreExecution

/-! Shift operators through the public source API (solcore-rs #129): `<<` and
`>>` on Words, their precedence between `+ -` and `&`, the compound `<<=` and
`>>=` on a local and on a mapping element, amounts at and past 256, and the two
adjacent tokens that spell them, so that nested type arguments still close with
two `>` tokens. Every expected value follows what the pinned Rust paths give
for Word shifts (lane D's probe and the `shift-operators` fixture, in
`docs/design/integer-types-unchecked-shifts.md`). -/
set_option autoImplicit false
namespace Tests.SourceCoreShiftExecution
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
  "function literalAmount(x: Word) returns (Word) { return x << 3; }",
  "function shiftLeft(x: Word, s: Word) returns (Word) { return x << s; }",
  "function shiftRight(x: Word, s: Word) returns (Word) { return x >> s; }",
  "function compound(x: Word, s: Word) returns (Word) { let r: Word = x; r <<= s; r >>= 1; return r; }",
  "function neverReverts(x: Word) returns (Word) { return x << 255; }",
  "function precedence(a: Word, b: Word) returns (Word) { return a + b << 2 & 0xff; }",
  "function comparisons(a: Word, b: Word) returns (Bool) { return a > b && a >= b; }",
  "function ladder(x: Word) returns (Word) { let w0: Word = x << 1 + 1; let w1: Word = x & 7 << 1; let w2: Word = x | 1 << 4; let w3: Word = 0; if (x >> 1 > 3) { w3 = 1; } let w4: Word = x << 2 * 3; let w5: Word = x ^ 1 << 2; return ((((w0 * 7 ^ w1) * 7 ^ w2) * 7 ^ w3) * 7 ^ w4) * 7 ^ w5; }",
  "function literals() returns (Word) { return 1 << 3 >> 1; }",
  "function shiftThenLess(a: Word, b: Word) returns (Bool) { return a << 1 < b; }",
  "function mapped(x: Word, s: Word) returns (Word) { let m: mapping(Bool => Word); m[true] = x; m[true] <<= s; m[true] >>= 1; return m[true]; }",
  "enum Box<T> { Box(T) }",
  "function nested(b: Box<Box<Word>>, x: Word) returns (Word) { return x >> 1; }"
]

private def names : List String :=
  ["literalAmount", "shiftLeft", "shiftRight", "compound", "neverReverts", "precedence",
    "comparisons", "ladder", "literals", "shiftThenLess", "mapped"]

private def seed (program : CheckedProgram) (name : String) : IO Seed :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
  | _ => throw (IO.userError s!"shift fixture missing {name}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value) :
    IO (Completion artifact) := do
  let executed ← session.runWithReceipt key arguments {executionFuel := 300000}
  match executed.val with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"shift export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"shift language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "shift execution exhausted")
  | .error error => throw (IO.userError s!"shift invocation: {reprStr error}")
private def boot (artifact : Artifact) : IO (Session artifact) := do
  let fresh ← artifact.bootstrapWithReceipt
  match fresh.val.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"shift bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "shift bootstrap exhausted")

/-- `x << 1 + 1`, `x & 7 << 1`, `x | 1 << 4`, `x >> 1 > 3`, `x << 2 * 3` and
`x ^ 1 << 2`, folded as the probe's `wordprec` method folds them. -/
private def ladderCases : List (Nat × Nat) :=
  [(0, 5492), (1, 72614), (3, 199304), (7, 472700), (8, 545277), (9, 592927),
    (255, 17116277), (high, 5541), (maximum, 52853)]

private def rejected (label : String) (lines : List String) : IO Unit :=
  match checkProgram (workspaceOf lines) with
  | .ok _ => throw (IO.userError s!"{label} was accepted")
  | .error _ => pure ()

def run : IO Unit := do
  let program ← get "shift check" (checkProgram workspace)
  let seeds ← names.mapM (seed program)
  let compiled ← get "shift compilation"
    (compile workspace seeds {specializationBudget := 256, compilationFuel := 1000})
  let key (index : Nat) : IO Key := match compiled.keys[index]? with
    | some key => pure key | none => throw (IO.userError "shift root missing")
  let mut session ← boot (← compiled.open)
  let wordCases : List (Nat × List Nat × Nat) :=
    [(0, [5], 40),
      (1, [1, 255], high), (1, [1, 256], 0), (1, [3, 1], 6), (1, [1, maximum], 0),
      (1, [maximum, 1], maximum - 1), (1, [0x100, 300], 0),
      (2, [high, 255], 1), (2, [maximum, 256], 0), (2, [0x100, 4], 0x10), (2, [0x100, 255], 0),
      (2, [maximum, maximum], 0), (2, [maximum, 3], maximum / 8),
      (3, [1, 8], 128), (3, [1, 300], 0),
      (4, [maximum], high),
      (5, [1, 2], 12), (5, [0x40, 0], 0),
      (8, [], 4),
      (10, [3, 4], 24), (10, [1, 256], 0), (10, [maximum, 1], high - 1)]
  for (index, arguments, expected) in wordCases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == word expected)
      s!"shift case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  for (input, expected) in ladderCases do
    let completed ← execute session (← key 7) [word input]
    require (completed.value == word expected) s!"shift precedence ladder {input} gave {reprStr completed.value}"
    session := completed.session
  let booleanCases : List (Nat × List Nat × Bool) :=
    [(6, [2, 1], true), (6, [1, 2], false), (9, [1, 3], true), (9, [2, 3], false)]
  for (index, arguments, expected) in booleanCases do
    let completed ← execute session (← key index) (arguments.map word)
    require (completed.value == .bool expected)
      s!"shift case {names[index]?} {arguments} gave {reprStr completed.value}"
    session := completed.session
  rejected "a shift spelled with separated tokens"
    ["function bad(a: Word, b: Word) returns (Word) { return a < < b; }"]
  rejected "a compound shift spelled with separated tokens"
    ["function bad(a: Word, b: Word) returns (Word) { a > >= b; return a; }"]
  rejected "a shift of a Bool"
    ["function bad(b: Bool) returns (Bool) { return b << 1; }"]
  rejected "a shift by a Bool"
    ["function bad(a: Word, b: Bool) returns (Word) { return a >> b; }"]
  IO.println "SOURCE_CORE_SHIFTS_PASS: Word `<<` and `>>` by amounts up to 2^256 - 1, their precedence between `+ -` and `&`, compound `<<=` and `>>=` on locals and mapping elements, nested type arguments closing with `>>`, and separated tokens rejected"

end Tests.SourceCoreShiftExecution
