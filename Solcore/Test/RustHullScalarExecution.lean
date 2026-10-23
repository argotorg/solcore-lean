import Solcore.Frontend.RustHull.ScalarExecutionSafety

set_option autoImplicit false
namespace Tests.RustHullScalarExecution
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def expectInput (type : Core.Ty) (input : String) (expected : Core.Expr) : IO Unit := do
  let actual ← get s!"input {input}" (ScalarExecution.parseInput type input)
  require (actual == expected) s!"input {input}: incorrect parsed value"
private def expectError {α : Type} (label message : String) (result : LowerM α) : IO Unit :=
  match result with
  | .error error => require (error.message == message) s!"{label}: wrong error {error.message}"
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")
private def reference (name : String) (type : Ty) : Expr := ⟨type, .var name, none⟩
private def pair (left right : Expr) : Expr := ⟨.product left.ty right.ty, .pair left right, none⟩
private def unit : Expr := ⟨.unit, .unit, none⟩
private def returned (value : Expr) : Stmt := ⟨.returnStmt value, none⟩
private def program (function : Function) : Program :=
  {functions := [function], entryPoints := [function.name], objects := []}
private def mixed : Program :=
  let value := pair (reference "w" .word)
    (pair (reference "b" .bool) (pair (reference "u" .unit) (reference "s" (.sum .unit .unit))))
  program {
    name := "mixed"
    args := [⟨"w", .word, none⟩, ⟨"b", .bool, none⟩, ⟨"u", .unit, none⟩, ⟨"s", .sum .unit .unit, none⟩]
    ret := value.ty
    body := [returned value]}
private def prepare (program : Program) (entry : String) (inputs : List String) : IO ScalarExecution.Prepared :=
  match ScalarExecution.prepare program entry inputs with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"preparation: {reprStr error}")
private def expectRun (label : String) (actual : Core.StatefulRunResult) (expected : Core.Value) : IO Unit :=
  match actual with
  | .done value _ => require (value == expected) s!"{label}: wrong result {reprStr value}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def resumeChunks : Nat → Core.StatefulRunResult → IO Core.StatefulRunResult
  | 0, _ => throw (IO.userError "scalar resume budget exhausted")
  | fuel + 1, result => match result with
      | .outOfFuel state => resumeChunks fuel (ScalarExecution.resume state 17)
      | _ => pure result

def run : IO Unit := do
  for text in ["42", "0x2a", "0X2A", "00042", toString (Core.wordModulus + 42)] do
    expectInput .word text (.word (word 42))
  expectInput .bool "true" (.bool true)
  expectInput .bool "false" (.bool false)
  expectInput (.sum .unit .unit) "true" (.inRight .unit .unit)
  expectInput (.sum .unit .unit) "false" (.inLeft .unit .unit)
  expectInput .unit "unit" .unit
  for type in [Core.Ty.bool, .sum .unit .unit] do
    for input in ["True", "FALSE", "1", "0", " true", ""] do
      expectError "Boolean spelling" "Boolean input must be true or false" (ScalarExecution.parseInput type input)
  expectError "unit spelling" "Unit input must be unit" (ScalarExecution.parseInput .unit "()")
  for type in [Core.Ty.integer, .product .word .word, .function .unit .unit,
      .sum .word .unit, .sum .unit .bool, .cell .word, .namedData ⟨0⟩] do
    expectError "unsupported input layout" "CLI input supports Word, Bool and Unit"
      (ScalarExecution.parseInput type "0")
  for input in ["", "0x", "-1", "0xgg", "1 "] do
    match ScalarExecution.parseInput .word input with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid Word accepted: {input}")
  expectError "count before value parsing" "argument count mismatch"
    (ScalarExecution.parseArguments [.word, .word] ["invalid"])
  expectError "extra input before value parsing" "argument count mismatch"
    (ScalarExecution.parseArguments [.word] ["invalid", "42"])
  require ((← get "empty argument bundle" (ScalarExecution.parseArguments [] [])) == .unit)
    "zero arguments did not use unit"
  require ((← get "single argument bundle" (ScalarExecution.parseArguments [.word] ["42"])) == .word (word 42))
    "one argument acquired an extra pair"
  let prepared ← prepare mixed "mixed" ["0x2a", "true", "unit", "false"]
  let value := Core.Value.pair (.word (word 42)) (.pair (.bool true) (.pair .unit (.inLeft .unit .unit)))
  let expected := Core.Value.inRight .word value
  expectRun "mixed scalar preparation" (ScalarExecution.run prepared) expected
  let initial := ScalarExecution.run prepared 0
  match initial with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero-fuel scalar invocation did not suspend")
  expectRun "repeated scalar resumption" (← resumeChunks 1000 initial) expected
  let empty ← prepare (program {name := "unit", args := [], ret := .unit, body := [returned unit]}) "unit" []
  expectRun "zero-argument entry" (ScalarExecution.run empty) (.inRight .word .unit)
  let single ← prepare (program {
    name := "word"
    args := [⟨"w", .word, none⟩]
    ret := .word
    body := [returned (reference "w" .word)]}) "word" [toString (Core.wordModulus + 7)]
  expectRun "single Word modulo input" (ScalarExecution.run single) (.inRight .word (.word (word 7)))
  let missingReturn ← prepare (program {name := "missing", args := [], ret := .word, body := []}) "missing" []
  expectRun "language failure remains an explicit result" (ScalarExecution.run missingReturn)
    (.inLeft .word (.word (word 4)))
  match ScalarExecution.prepare mixed "absent" [] with
  | .error (.lowering _) => pure ()
  | _ => throw (IO.userError "missing entry did not retain lowering error stage")
  match ScalarExecution.prepare mixed "mixed" [] with
  | .error (.input error) => require (error.message == "argument count mismatch") "wrong input-stage error"
  | _ => throw (IO.userError "wrong count did not retain input error stage")
  let looping := program {
    name := "loop"
    args := []
    ret := .unit
    body := [⟨.expression ⟨.unit, .call "loop" [], none⟩, none⟩]}
  let looping ← prepare looping "loop" []
  match ScalarExecution.run looping 1000 with
  | .outOfFuel state =>
      match ScalarExecution.resume state 1000 with
      | .outOfFuel _ => pure ()
      | other => throw (IO.userError s!"recursive resumption: {reprStr other}")
  | other => throw (IO.userError s!"recursive execution: {reprStr other}")

end Tests.RustHullScalarExecution
