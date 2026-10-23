import Solcore.Frontend.RustHull.Ambient
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullAmbient
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Solcore.Core.Expr := .word (word value)
private def get {α : Type} (result : LowerM α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def scope : Scope := Ambient.slots.reverse.map fun (name, type) =>
  ⟨some ("$lean$evm$" ++ name), type, false⟩

private def allocate (context : Ambient.Context) (body : Solcore.Core.Expr) : Solcore.Core.Expr :=
  .letE (Ambient.contextExpression context)
    (Ambient.slots.zipIdx.foldr (fun ((_, type), index) body =>
      .letE (.newCell type (Ambient.initialValue index (.var index))) body) body)

private def program (context : Ambient.Context) (name : String)
    (arguments : List Solcore.Core.Expr := []) : IO Solcore.Core.Program := do
  let lowered ← get (Ambient.lowerBuiltin scope name arguments)
  pure {
    resultType := LanguageResult.resultType .word,
    dataDefinitions := Memory.definitions, body := allocate context lowered.expression}

private def result (label : String) (compiled : Solcore.Core.Program) (expected : Value) : IO Unit := do
  require compiled.check s!"{label}: ambient Core is ill-typed"
  match compiled.runStateful 100000 with
  | .done actual _ => require (actual == expected) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def expect (label : String) (context : Ambient.Context) (name : String)
    (arguments : List Nat) (expected : Nat) : IO Unit := do
  result label (← program context name (arguments.map number)) (.inRight .word (.word (word expected)))

private def unavailable (label : String) (context : Ambient.Context) (name : String)
    (arguments : List Nat := []) : IO Unit := do
  result label (← program context name (arguments.map number))
    (.inLeft .word (.word Ambient.unavailableReason))

private def fieldTests : IO Unit := do
  let high := 2 ^ 200
  let context : Ambient.Context := {
    origin := some (word (high + 0xabc)), gasprice := some (word 7),
    coinbase := some (word (high + 0xdef)), timestamp := some (word 123456),
    number := some (word 300), prevrandao := some Word.maximum,
    gaslimit := some (word 30000000), chainid := some (word 1),
    basefee := some (word 9), blobbasefee := some (word 11)}
  for (name, expected) in [("origin", 0xabc), ("gasprice", 7), ("coinbase", 0xdef),
      ("timestamp", 123456), ("number", 300), ("prevrandao", wordModulus - 1),
      ("gaslimit", 30000000), ("chainid", 1), ("basefee", 9), ("blobbasefee", 11)] do
    expect s!"provided {name}" context name [] expected
    unavailable s!"missing {name}" {} name
    match Ambient.lowerBuiltin scope name [number 0] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: wrong arity accepted")
  expect "supplied zero differs from missing" {origin := some Word.zero} "origin" [] 0
  expect "address maximum mask" {coinbase := some Word.maximum} "coinbase" [] (2 ^ 160 - 1)
  require (!Ambient.supports "gas" && !Ambient.supports "unknown") "ambient support list overreaches"
  require (Ambient.slots.length = 12) "ambient context slot count changed"

private def blockTests : IO Unit := do
  let context : Ambient.Context := {
    number := some (word 300), blockHashes := some [
      (word 299, word 0xa1), (word 44, word 0xa2), (word 43, word 0xa3),
      (word 300, word 0xa4), (word 301, word 0xa5), (Word.maximum, word 0xa6)]}
  for (index, expected) in [(299, 0xa1), (44, 0xa2), (43, 0), (300, 0),
      (301, 0), (298, 0), (wordModulus - 1, 0)] do
    expect s!"block hash at {index}" context "blockhash" [index] expected
  expect "genesis cannot wrap to maximum block"
    {number := some Word.zero, blockHashes := some [(Word.maximum, word 77)]}
    "blockhash" [wordModulus - 1] 0
  expect "maximum current number accepts preceding block"
    {number := some Word.maximum,
      blockHashes := some [(word (wordModulus - 2), word 88)]}
    "blockhash" [wordModulus - 2] 88
  expect "maximum current number cannot wrap a far history distance"
    {number := some Word.maximum, blockHashes := some [(Word.zero, word 99)]}
    "blockhash" [0] 0
  expect "supplied empty history" {number := some (word 1), blockHashes := some []}
    "blockhash" [0] 0
  unavailable "block hash requires current number" {blockHashes := some []} "blockhash" [0]
  unavailable "block hash requires history model" {number := some (word 1)} "blockhash" [0]
  unavailable "even excluded range requires explicit history" {number := some (word 1)} "blockhash" [1]

private def blobTests : IO Unit := do
  let context : Ambient.Context := {blobHashes := some [word 0x11, Word.zero, word 0x33]}
  for (index, expected) in [(0, 0x11), (1, 0), (2, 0x33), (3, 0), (wordModulus - 1, 0)] do
    expect s!"blob hash at {index}" context "blobhash" [index] expected
  expect "supplied empty blob list" {blobHashes := some []} "blobhash" [0] 0
  unavailable "missing blob list" {} "blobhash" [0]
  for name in ["blockhash", "blobhash"] do
    match Ambient.lowerBuiltin scope name [] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: missing index accepted")
    match Ambient.lowerBuiltin scope name [number 0, number 1] with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"{name}: excess index accepted")

private def resumeChunks : Nat → State → IO Value
  | 0, _ => throw (IO.userError "ambient resume budget exhausted")
  | attempts + 1, state => match runStateful 29 state with
      | .done value _ => pure value
      | .outOfFuel state => resumeChunks attempts state
      | .fault error _ => throw (IO.userError s!"ambient resume fault: {reprStr error}")

private def onceAndResumeTests : IO Unit := do
  let context : Ambient.Context := {
    number := some (word 1), blockHashes := some [(Word.zero, word 0xabc)],
    blobHashes := some [word 0xabc]}
  for name in ["blockhash", "blobhash"] do
    let index : Solcore.Core.Expr := .letE
      (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (number 0)
    let lowered ← get (Ambient.lowerBuiltin (scope.temporary (.cell .word)) name [index])
    let compiled : Solcore.Core.Program := {
      resultType := .product (LanguageResult.resultType .word) .word,
      dataDefinitions := Memory.definitions,
      body := allocate context (.letE (.newCell .word (number 0))
        (.letE lowered.expression (.pair (.var 0) (.loadCell (.var 1)))))}
    let expected := Value.pair (.inRight .word (.word (word 0xabc))) (.word (word 1))
    result s!"{name} evaluates index once" compiled expected
    match compiled.runStateful 1 with
    | .outOfFuel checkpoint =>
        require ((← resumeChunks 1000 checkpoint) == expected) s!"{name}: resumption changed result"
    | other => throw (IO.userError s!"{name}: expected suspension, got {reprStr other}")

def run : IO Unit := do
  fieldTests
  blockTests
  blobTests
  onceAndResumeTests
  IO.println "Rust Hull ambient context tests passed"

end Tests.RustHullAmbient
