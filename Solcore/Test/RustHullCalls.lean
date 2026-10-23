import Solcore.Frontend.RustHull.Calls
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullCalls
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def ok (value : Nat) : Value := .inRight .word (scalar value)

private structure Call where
  depth : Nat := 0
  source : Nat := 7
  length : Nat := 65
  destination : Nat := 8
  outputLength : Nat := 17
  static : Bool := false
  installed : Bool := true
  success : Bool := true
  fail : Bool := false
  mutate : Bool := false
  tick : Bool := false

private def callbackBody (call : Call) : Expr :=
  let request := Expr.var 0
  let reject := LanguageResult.failure Calls.responseType (number 99)
  let result := if call.fail then reject else
    LanguageResult.success (Calls.response (.bool call.success)
      (Calls.requestField 6 request) (Calls.requestField 7 request))
  let result := if call.mutate then LocalSequence.discard Calls.responseType
    (Memory.mstore8 (.var 6) (.var 5) (number 0) (number 0xee)) result else result
  let checks := [(0, 0xabc), (1, 0xdef), (2, 17), (4, call.depth + 1), (5, 88), (7, call.length)]
  let checked : Expr := checks.foldr (fun (index, expected) next =>
    .ifE (.binary .wordEq (Calls.requestField index request) (number expected)) next reject)
    (.ifE (Calls.requestField 3 request) (if call.static then result else reject)
      (if call.static then reject else result))
  .letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (number 1)))
    (checked.weakenAt 0)

/-- In the body: counter0, callback1, return size2, return map3, memory size4,
memory5. The callback captures these cells and receives its request at zero. -/
private def invoke (call : Call) : Expr :=
  let tick (value : Expr) := if call.tick then
    Expr.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1)))
      (value.weakenAt 0) else value
  Calls.invoke (tick (.var 5)) (tick (.var 4)) (tick (.var 3)) (tick (.var 2)) (tick (.var 1))
    (tick (number (2 ^ 200 + 0xdef))) (tick (number call.depth)) (tick (.bool call.static))
    (tick (number 88)) (tick (number (2 ^ 200 + 0xabc))) (tick (number 17))
    (tick (number call.source)) (tick (number call.length))
    (tick (number call.destination)) (tick (number call.outputLength))

private def program (input : List UInt8) (call : Call) : Program :=
  let body := if call.installed then
    Expr.letE (.storeCell (.var 1) (.inRight .unit
      (.lambda Calls.requestType (LanguageResult.resultType Calls.responseType) (callbackBody call))))
      ((invoke call).weakenAt 0) else invoke call
  {resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
   body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
      (.letE (.newCell .word (number 0))
        (.letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes [0xaa, 0xbb])))
          (.letE (.newCell .word (number 2))
            (.letE (OptionalCell.allocate Calls.callbackType)
              (.letE (.newCell .word (number 0)) body)))))}

private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "invalid empty map"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "invalid map constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid map value"

private def checkMap (label : String) (actual : Option Value) (expected : List UInt8) : IO Unit := do
  let some actual := actual | throw (IO.userError s!"{label}: missing cell")
  let actual ← match entries actual with
    | .ok actual => pure actual
    | .error error => throw (IO.userError s!"{label}: {error}")
  let expected := Memory.packBytes expected
  for (key, _) in actual ++ expected do
    require (WordMapping.lookupEntries key actual == WordMapping.lookupEntries key expected)
      s!"{label}: wrong packed word at {key.val}"

private def verify (label : String) (expected : Value) (memory returned : List UInt8)
    (size count : Nat) (actual : StatefulRunResult) : IO Unit :=
  match actual with
  | .done value store => do
      require (value == expected) s!"{label}: {reprStr value}"
      checkMap s!"{label} memory" store[0]? memory
      require (store[1]? == some (scalar size)) s!"{label}: memory extent"
      checkMap s!"{label} return data" store[2]? returned
      require (store[3]? == some (scalar returned.length)) s!"{label}: return data extent"
      require (store[5]? == some (scalar count)) s!"{label}: argument/callback count"
  | .outOfFuel _ => throw (IO.userError s!"{label}: exhausted test fuel")
  | .fault error _ => throw (IO.userError s!"{label}: {reprStr error}")

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "call resume budget exhausted")
  | fuel + 1, state => match runStateful 500 state with
      | .outOfFuel state => resumeChunks fuel state
      | result => pure result

private def overwritten (input : List UInt8) (offset : Nat) (replacement : List UInt8) : List UInt8 :=
  let padded := input ++ List.replicate (offset + replacement.length - input.length) 0
  padded.take offset ++ replacement ++ padded.drop (offset + replacement.length)

private def check (label : String) (input : List UInt8) (call : Call) (expected : Value)
    (memory returned : List UInt8) (size count : Nat) (resume : Bool := false) : IO Unit := do
  let compiled := program input call
  require compiled.check s!"{label}: ill-typed Core"
  verify label expected memory returned size count (compiled.runStateful 2000000)
  if resume then
    match compiled.runStateful 100 with
    | .outOfFuel state => verify s!"{label} resumed" expected memory returned size count (← resumeChunks 10000 state)
    | _ => throw (IO.userError s!"{label}: fixture did not suspend")

def run : IO Unit := do
  let input := (List.range 160).map fun index => UInt8.ofNat (index * 7 + 3)
  let payload := (input.drop 7).take 65
  for succeeded in [true, false] do
    check s!"nested {(if succeeded then "return" else "revert")} bytes and clipped overlapping output"
      input {success := succeeded, tick := true} (ok (if succeeded then 1 else 0))
      (overwritten input 8 (payload.take 17)) payload 96 16 true
  check "input snapshot survives callback memory writes" input {mutate := true}
    (ok 1) (overwritten (overwritten input 0 [0xee]) 8 (payload.take 17)) payload 96 1
  check "static flag and child depth1024" input {depth := 1023, static := true}
    (ok 1) (overwritten input 8 (payload.take 17)) payload 96 1
  for depth in [1024, wordModulus - 1] do
    check s!"depth{depth} refuses child and clears return data" input {depth}
      (ok 0) input [] 96 0
  check "empty ranges ignore maximal offsets" input
    {source := wordModulus - 1, length := 0, destination := wordModulus - 1, outputLength := 0}
    (ok 1) input [] 0 1
  check "short return data leaves output suffix untouched" input {length := 3, outputLength := 65}
    (ok 1) (overwritten input 8 ((input.drop 7).take 3)) ((input.drop 7).take 3) 96 1
  check "no output keeps full return data" input {destination := wordModulus - 1, outputLength := 0}
    (ok 1) input payload 96 1
  check "callback unavailable" input {installed := false}
    (.inLeft .word (.word Calls.unavailableReason)) input [] 96 0
  check "callback language failure propagates" input {fail := true}
    (.inLeft .word (scalar 99)) input [] 96 1
  check "invalid input range does not start call" input
    {source := wordModulus - 16, length := 32}
    (.inLeft .word (.word Memory.overflowReason)) input [0xaa, 0xbb] 0 0
  check "invalid output range does not start call" input
    {source := 0, length := 1, destination := wordModulus - 16, outputLength := 32}
    (.inLeft .word (.word Memory.overflowReason)) input [0xaa, 0xbb] 32 0

end Tests.RustHullCalls
