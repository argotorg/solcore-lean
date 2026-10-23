import Solcore.Frontend.RustHull.Logs
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullLogs
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false
private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)
private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def types : List Ty → Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (types rest)
private def sequence (action next : Expr) : Expr := LanguageResult.bind .unit action (next.weakenAt 0)

/-- In the body: cursor0, logs1, memory size2, memory3. -/
private def program (input : List UInt8) (body : Expr) (cursor : Nat := 0)
    (logs : WordMapping.Entries := []) : Program := {
  resultType := types [LanguageResult.resultType .unit, WordMapping.type, .word, .word, WordMapping.type]
  dataDefinitions := Memory.definitions
  body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
    (.letE (.newCell .word (number 0))
      (.letE (.newCell WordMapping.type (WordMapping.literal logs))
        (.letE (.newCell .word (number cursor))
          (.letE body (packet [.var 0, .loadCell (.var 2), .loadCell (.var 1),
            .loadCell (.var 3), .loadCell (.var 4)])))))
}

private def emit (address : Nat) (topics : List Nat) (offset length : Nat) : Expr :=
  Logs.append (.var 3) (.var 2) (.var 1) (.var 0) (number address) (topics.map number) (number offset) (number length)

private structure Result where
  events : List Logs.Event
  cursor : Nat
  size : Nat
  memory : Value

private def result (label : String) (actual : Value) : IO Result := do
  let .pair status (.pair mapping (.pair (.word cursor) (.pair (.word size) memory))) := actual
    | throw (IO.userError s!"{label}: malformed snapshot")
  require (status == .inRight .word .unit) s!"{label}: emission failed: {reprStr status}"
  let events ← get (Logs.decodeValues mapping (.word cursor))
  pure {events, cursor := cursor.val, size := size.val, memory}

private def execute (label : String) (compiled : Program) : IO Result := do
  require compiled.check s!"{label}: ill-typed log Core"
  match compiled.runStateful 5000000 with
  | .done value _ => result label value
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def failure (label : String) (compiled : Program) (reason : Word) (cursor : Nat)
    (logs : WordMapping.Entries) : IO Unit := do
  require compiled.check s!"{label}: ill-typed rejected emission"
  match compiled.runStateful 10000 with
  | .done actual _ =>
      require (actual == .pair (.inLeft .unit (.word reason))
        (.pair (WordMapping.encode logs) (.pair (scalar cursor)
          (.pair (scalar 0) (WordMapping.encode [])))))
        s!"{label}: failure changed log or memory state: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: failure did not finish: {reprStr other}")

private def words (values : List Nat) : WordMapping.Entries :=
  values.zipIdx.map fun (value, index) => (word index, word value)

private def resumeChunks : Nat → State → IO Value
  | 0, _ => throw (IO.userError "log resumption did not finish within its budget")
  | attempts + 1, state => match runStateful 500 state with
      | .done value _ => pure value
      | .outOfFuel state => resumeChunks attempts state
      | .fault error _ => throw (IO.userError s!"log resumption fault: {reprStr error}")

def run : IO Unit := do
  let input := (List.range 160).map fun index => UInt8.ofNat (37 * index + 11)
  for count in List.range 5 do
    let topics := (List.range count).map (fun index => 0x1234 + 19 * index)
    let actual ← execute s!"log{count}" (program input (emit 0xabcd topics 7 65))
    require (actual.events == [{address := word 0xabcd, topics := topics.map word, data := (input.drop 7).take 65}])
      s!"log{count}: address, topics or snapshot differ"
    require (actual.cursor = 3 + count + 3 && actual.size = 96) s!"log{count}: wrong stream or memory extent"
    require (actual.memory == WordMapping.encode (Memory.packBytes input)) s!"log{count}: input memory changed"
  for length in [0, 1, 31, 32, 33, 63, 64, 65, 129] do
    let actual ← execute s!"data length{length}" (program input (emit 1 [] 7 length))
    require (actual.events == [{address := word 1, topics := [], data := (input.drop 7).take length}])
      s!"data length{length}: wrong bytes or padding"
    require (actual.cursor = 3 + (length + 31) / 32) s!"data length{length}: wrong log word count"
    require (actual.size = if length = 0 then 0 else (length + 7 + 31) / 32 * 32)
      s!"data length{length}: wrong memory size"
  let zero ← execute "empty max offset" (program [] (emit 2 [9] (wordModulus - 1) 0))
  require (zero.events == [{address := word 2, topics := [word 9], data := []}] && zero.size = 0)
    "empty data accessed the maximum offset"
  let ordered := program input (sequence (emit 10 [100] 0 33)
    (sequence (Memory.mstore8 (.var 3) (.var 2) (number 0) (number 0xee)) (emit 11 [101, 102] 0 33)))
  let actual ← execute "ordered snapshots" ordered
  let expected : List Logs.Event := [
    {address := word 10, topics := [word 100], data := input.take 33},
    {address := word 11, topics := [word 101, word 102], data := UInt8.ofNat 0xee :: (input.drop 1).take 32}]
  require (actual.events == expected) "later memory writes changed prior logs or emission order"
  require (actual.cursor = 13) "ordered emission cursor is incorrect"
  failure "memory overflow" (program [] (emit 0 [] (wordModulus - 16) 32)) Memory.overflowReason 0 []
  failure "topic count" (program [] (emit 0 [0, 1, 2, 3, 4] 0 1)) Logs.topicReason 0 []
  failure "cursor overflow precedes memory expansion"
    (program [] (emit 0 [] 0 1) (wordModulus - 3)) Logs.capacityReason (wordModulus - 3) []
  let initialLogs := words [1, 0, 0]
  failure "cursor overflow preserves existing logs"
    (program [] (emit 0 [] 0 0) (wordModulus - 2) initialLogs)
    Logs.capacityReason (wordModulus - 2) initialLogs
  match ordered.runStateful 100 with
  | .outOfFuel state =>
      let resumed ← result "chunked resume" (← resumeChunks 1000 state)
      require (resumed.events == expected && resumed.cursor = 13) "resumption changed captured events"
  | other => throw (IO.userError s!"log should suspend: {reprStr other}")
  let valid := words [0x12, 1, 1, 0x34, 0xab * 256 ^ 31]
  require ((← get (Logs.decode valid (word 5))) ==
    [{address := word 0x12, topics := [word 0x34], data := [UInt8.ofNat 0xab]}]) "decoder valid record"
  require (Logs.decode valid (word 5) 0 |> rejected) "decoder ignored log count limit"
  require (Logs.decode valid (word 5) 10 0 |> rejected) "decoder ignored byte limit"
  require (Logs.decode valid (word 4) |> rejected) "decoder accepted truncated payload"
  require (Logs.decode (words [1, 5, 0]) (word 3) |> rejected) "decoder accepted five topics"
  require (Logs.decode (words [1, 0, 1, 1]) (word 4) |> rejected) "decoder accepted nonzero padding"
  require (Logs.decode valid.tail (word 5) |> rejected) "decoder accepted a missing header word"
  require (Logs.decode ((word 0, word 99) :: valid) (word 5) |> rejected) "decoder accepted duplicate live keys"
  require (Logs.decode (valid.take 1 ++ [(word 0, word 99)] ++ valid.drop 2) (word 5) |> rejected)
    "decoder accepted duplicate keys with the expected stream length"
  require (Logs.decode (valid.take 4 ++ [(word 5, Word.zero)]) (word 5) |> rejected)
    "decoder accepted a key beyond the cursor"
  require (Logs.decodeValues .unit (.word Word.zero) |> rejected) "decoder accepted malformed mapping"
  let byteLimit := 1048576
  let large := words ([0x12, 0, byteLimit] ++ List.replicate (byteLimit / 32) 0)
  let decoded ← get (Logs.decode large (word (3 + byteLimit / 32)))
  let [event] := decoded | throw (IO.userError "decoder split a large event")
  require (event.data.length = byteLimit && event.data.all (· == 0))
    "decoder failed at its full payload export limit"

end Tests.RustHullLogs
