import Solcore.Frontend.RustHull.Sha256
import Solcore.Frontend.RustHull.Ripemd160
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.Keccak
import Solcore.Abi.Keccak256
import Solcore.Frontend.RustHull.Logs
import Solcore.Frontend.RustHull.Memory
import Solcore.Frontend.RustHull.P256
import Solcore.Core.Check
import Lean
import Solcore.Frontend.RustHull.Precompiles
import Solcore.Frontend.RustHull.Secp256k1
import Solcore.Frontend.RustYulPrimitives

/-!
# Hull runtime tests

Primitives of the Hull runtime on Core: memory, logs, hashes, Keccak and precompiles.
-/

section
-- leanmerge: from Solcore.Test.RustHullHashes
set_option autoImplicit false
namespace Tests.RustHullHashes
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private abbrev Hash := Expr → Expr → Expr → Expr → Expr

private def program (hash : Hash) (input : List UInt8) (offset count : Nat) : Program := {
  resultType := .product (LanguageResult.resultType .word) .word
  dataDefinitions := Memory.definitions
  body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input offset)))
    (.letE (.newCell .word (number 0))
      (.pair (hash (.var 1) (.var 0) (number offset) (number count)) (.loadCell (.var 0))))
}

private def check (label : String) (hash : Hash) (input : List UInt8) (expected : Nat)
    (offset : Nat := 0) : IO Unit := do
  let compiled := program hash input offset input.length
  require compiled.check s!"{label}: hash produced ill-typed Core"
  match compiled.runStateful 20000000 with
  | .done actual store =>
      let memorySize := if input.isEmpty then 0 else ((offset + input.length + 31) / 32) * 32
      require (actual == .pair (.inRight .word (scalar expected)) (scalar memorySize))
        s!"{label}: wrong hash or memory extent: {reprStr actual}"
      require (store[0]? == some (WordMapping.encode (Memory.packBytes input offset)))
        s!"{label}: hashing changed input memory"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

/-- Boundary vectors generated independently with Python hashlib/OpenSSL;
input byte i is (37*i+11) mod 256. Published empty/abc vectors are also checked. -/
private def vectors : List (Nat × Nat × Nat) := [
  (0, 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855, 0x9c1185a5c5e9fc54612808977ee8f548b2258d31),
  (1, 0xe7cf46a078fed4fafd0b5e3aff144802b853f8ae459a4f0c14add3314b7cc3a6, 0xe257e7861ba1b82bdcff75ff2bb1613d83b797bd),
  (31, 0x0cc420417cb6a768e632bf1be8d1f197c9c0e9dd1dd2021e3bd37c46cee0516f, 0x1078ea07048643129aeb91ed28e495723c52265c),
  (32, 0x83b7a8ed859053c81d818870fab1f8b1ae44d06a98a9665d369a8fd7d2838ded, 0x36781d5c249ba2f726af6d7f101dea2b4164b603),
  (55, 0x2900465fcb533e05a158fd2b3be0e5e3b03740d83060aa3580e0d98a96bf2384, 0xcb9a91b689c2e5a5aff392733f33c8fb75998dbb),
  (56, 0x31454ff48ef36af2f08fd511bdc37d9d5855ac23e992e5ff5445cb6b7674a674, 0x0fde8285ccc694b28a3205e30e3153c3f2a2dfa2),
  (63, 0x5f6401b96532c36de4e65beec0409b69b1d181864c8009b7a04f43e5d56350d1, 0x28d9c6a82ecf3196a0c5ab9cd79053118ca43301),
  (64, 0x94eb5de4943613fd048dc93393ab06877405faa39c11f53e9386083339833e7e, 0xc9b1871a7c604823d7cc8cc48e4ea37a4f841001),
  (65, 0xfc518669b6eb4b4dd91827ecacef86689c725bd5bab888fd3b26dbb196eec954, 0x26bc5a01292f459c7bd3310eaf53b72d25df1e71),
  (119, 0xb0dc41b1a384e2f1203f0351b38fbeaafceef577ce1191d5bfc25da39f721eae, 0x3e51052aaeaf2b4b120980b0c3c79f26301ff2f9),
  (120, 0x5df24dd802ac26132ce608dcb5f09841eef039ee0f152acf98d26d17fe4e88e6, 0x0268020acd3f91628e14766d7791dbf683bff67d),
  (127, 0x0fe729ff19257bd6fec853acc2ea355f6b34b58e6c0f684c3e188fcdfcd9baae, 0x24ba60dff396cf212ad4c3969eb1e281f044a7b0),
  (128, 0x0aedd4856f8eba0963627336ad5144a9a7dbe12498e6066f0165fc97d8ddee4c, 0x2349a24ad9bd73b09329b1c014c333610548ac55),
  (129, 0x4f1757ae4bffbae86d775b831765b75af154d52f7deaa46dd378051a2d3ad57f, 0x5a83b0b39268fa523094d515def4dafe725d5930),
  (1024, 0xffbad8f947474cfdd5b2bb22d7e0bf5ee8ba2b7af859d0c2bb28622db6a4be47, 0xba940bb0f331e6c62ae7eead37a76d5c52c799ed)]

def run : IO Unit := do
  check "SHA256 abc" Sha256.hash "abc".toUTF8.toList
    0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  check "RIPEMD160 abc" Ripemd160.hash "abc".toUTF8.toList
    0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc
  for (length, sha, ripemd) in vectors do
    let input := (List.range length).map fun index => UInt8.ofNat (index * 37 + 11)
    check s!"SHA256 length{length}" Sha256.hash input sha
    check s!"RIPEMD160 length{length}" Ripemd160.hash input ripemd
    if length = 65 then
      check "SHA256 unaligned offset" Sha256.hash input sha 7
      check "RIPEMD160 unaligned offset" Ripemd160.hash input ripemd 7
  check "SHA256 empty max offset" Sha256.hash []
    0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 (wordModulus - 1)
  check "RIPEMD160 empty max offset" Ripemd160.hash []
    0x9c1185a5c5e9fc54612808977ee8f548b2258d31 (wordModulus - 1)
  for (label, hash, expected) in [("SHA256", Sha256.hash,
      0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad),
      ("RIPEMD160", Ripemd160.hash, 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc)] do
    let resumable := program hash "abc".toUTF8.toList 0 3
    match resumable.runStateful 200 with
    | .outOfFuel state =>
        match runStateful 20000000 state with
        | .done actual _ =>
            require (actual == .pair (.inRight .word (scalar expected)) (scalar 32))
              s!"{label}: suspension changed the digest"
        | other => throw (IO.userError s!"{label}: failed resume: {reprStr other}")
    | _ => throw (IO.userError s!"{label}: hash did not suspend")
    let overflow := program hash [] (wordModulus - 16) 32
    require overflow.check s!"{label}: overflow expression is ill-typed"
    match overflow.runStateful 10000 with
    | .done actual store =>
        require (actual == .pair (.inLeft .word (.word Memory.overflowReason)) (scalar 0))
          s!"{label}: overflowing input range was accepted"
        require (store[0]? == some (WordMapping.encode [])) s!"{label}: overflow changed memory"
    | other => throw (IO.userError s!"{label}: unexpected overflow result {reprStr other}")

end Tests.RustHullHashes
end

section
-- leanmerge: from Solcore.Test.RustHullKeccak
set_option autoImplicit false

namespace Tests.RustHullKeccak
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def entries (bytes : List UInt8) (offset : Nat) : WordMapping.Entries :=
  Memory.packBytes bytes offset
private def expectedHash (bytes : List UInt8) : Word :=
  let hashed := Solcore.Abi.V1.Keccak256.hash bytes.toByteArray
  Word.ofNatModulo (hashed.data.foldl (fun value byte => value * 256 + byte.toNat) 0)

private def program (bytes : List UInt8) (offset : Nat := 0) (length : Nat := bytes.length) : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  dataDefinitions := Memory.definitions
  body := .letE (.newCell WordMapping.type (WordMapping.literal (entries bytes offset)))
    (.letE (.newCell .word (word 0))
      (LanguageResult.bind (.product .word .word)
        (Keccak.hash (.var 1) (.var 0) (word offset) (word length))
        (LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))))
}

private def expect (label : String) (bytes : List UInt8) (offset : Nat := 0) : IO Unit := do
  let compiled := program bytes offset
  require compiled.check s!"Keccak {label}: generated Core is ill-typed"
  let size := if bytes.isEmpty then 0 else ((offset + bytes.length + 31) / 32) * 32
  let expected := Value.inRight .word (.pair (.word (expectedHash bytes)) (scalar size))
  match compiled.runStateful 10000000 with
  | .done value store =>
      require (value == expected) s!"Keccak {label}: expected {reprStr expected}, got {reprStr value}"
      require (store[0]? == some (WordMapping.encode (entries bytes offset)))
        s!"Keccak {label}: hashing or padding changed memory"
  | .outOfFuel _ => throw (IO.userError s!"Keccak {label}: insufficient test fuel")
  | .fault error _ => throw (IO.userError s!"Keccak {label}: {reprStr error}")

def run : IO Unit := do
  require (expectedHash [] == Word.ofNatModulo
    0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    "reference empty Keccak vector changed"
  let abc := "abc".toUTF8.data.toList
  require (expectedHash abc == Word.ofNatModulo
    0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45)
    "reference abc Keccak vector changed"
  expect "empty" []
  expect "abc" abc
  expect "unaligned abc" abc 7
  for size in [31, 32, 135, 136, 137] do
    let bytes := (List.range size).map fun index => UInt8.ofNat (17 * index + 3)
    expect s!"{size} bytes" bytes
  expect "zero length at largest offset" [] (wordModulus - 1)

  let suspended := (program abc).runStateful 100
  match suspended with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ =>
          require (value == .inRight .word (.pair (.word (expectedHash abc)) (scalar 32)))
            "Keccak resumption changed the digest or memory size"
      | _ => throw (IO.userError "Keccak resumption did not finish")
  | _ => throw (IO.userError "Keccak test did not suspend")

  let overflow := program [] (wordModulus - 1) 1
  require overflow.check "Keccak overflow fixture is ill-typed"
  match overflow.runStateful 1000 with
  | .done value store =>
      require (value == .inLeft (.product .word .word) (.word Memory.overflowReason))
        "Keccak accepted an overflowing memory range"
      require (store[1]? == some (scalar 0)) "Keccak overflow expanded memory"
  | _ => throw (IO.userError "Keccak overflow fixture did not return a language failure")

end Tests.RustHullKeccak
end

section
-- leanmerge: from Solcore.Test.RustHullLogs
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
end

section
-- leanmerge: from Solcore.Test.RustHullMemory
set_option autoImplicit false

namespace Tests.RustHullMemory
open Solcore.Core
open Solcore.Frontend.RustHull

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Test bodies see the size cell at zero and the memory cell at one. -/
private def memory (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type WordMapping.empty)
    (.letE (.newCell .word (word 0)) body)

private def initialized (bytes : List UInt8) (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes bytes)))
    (.letE (.newCell .word (word 0)) body)

private def bytesWord (bytes : List UInt8) : Nat :=
  ((bytes ++ List.replicate 32 (0 : UInt8)).take 32).foldl
    (fun (value : Nat) (byte : UInt8) => value * 256 + byte.toNat) 0

private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def withSize (action : Expr) : Expr :=
  LanguageResult.bind (.product .word .word) action
    (LanguageResult.success (.pair (.var 0) (.loadCell (.var 1))))

private def expect (label : String) (result : Ty) (body : Expr) (value : Value) : IO Unit := do
  let program : Program := {
    resultType := LanguageResult.resultType result
    body
    dataDefinitions := Memory.definitions
  }
  require program.check s!"{label}: memory helper produced ill-typed Core"
  match program.run 3000000 with
  | .done actual => require (actual == .inRight .word value) s!"{label}: expected {reprStr value}, got {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

def run : IO Unit := do
  let maximum := wordModulus - 1
  let pattern := (List.range 32).foldl (fun value index => value * 256 + index + 1) 0
  expect "initial size" .word (memory (Memory.msize (.var 0))) (scalar 0)
  expect "zero-filled read expands size" (.product .word .word)
    (memory (withSize (Memory.mload (.var 1) (.var 0) (word 1))))
    (.pair (scalar 0) (scalar 64))
  expect "word round trip" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar pattern)
  expect "unaligned word round trip" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 1) (word pattern))
      (withSize (Memory.mload (.var 1) (.var 0) (word 1)))))
    (.pair (scalar pattern) (scalar 64))
  expect "unaligned zero prefix" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 1) (word pattern))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (pattern / 256))
  expect "big endian first byte" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (Memory.loadByte (.var 1) (.var 0) (word 0)))) (scalar 1)
  expect "mstore8 uses low byte" .word
    (memory (sequence .word (Memory.mstore8 (.var 1) (.var 0) (word 31) (word 0x1ab))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0xab)
  expect "byte overwrite preserves neighbors" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mstore8 (.var 1) (.var 0) (word 17) (word 0xab))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar (pattern + (0xab - 18) * 256 ^ 14))
  expect "cross-word byte overwrite" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 31) (word (0xab * 256 ^ 31)))
      (withSize (Memory.mload (.var 1) (.var 0) (word 0)))))
    (.pair (scalar 0xab) (scalar 64))
  expect "memory size never shrinks" .word
    (memory (sequence .word (Memory.touch (.var 0) (word 96) (word 1))
      (sequence .word (Memory.touch (.var 0) (word 0) (word 1)) (Memory.msize (.var 0)))))
    (scalar 128)
  expect "zero length ignores huge offset" .word
    (memory (sequence .word (Memory.touch (.var 0) (word maximum) (word 0))
      (Memory.msize (.var 0)))) (scalar 0)
  expect "calldata right padding" .word
    (Memory.readWord (WordMapping.literal [(Word.zero, Word.ofNatModulo 0x12),
      (Word.ofNatModulo 1, Word.ofNatModulo 0x34)]) (word 0))
    (scalar (0x1234 * 256 ^ 30))
  expect "calldata offset cannot wrap" .word
    (Memory.readWord (WordMapping.literal [(Word.zero, Word.ofNatModulo 0xff)]) (word maximum))
    (scalar 0)
  expect "copy overlaps to the right" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 1) (word 0) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar (256 ^ 31 + pattern / 256))
  expect "copy overlaps to the left" .word
    (memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 0) (word 1) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0)))))
    (scalar ((pattern * 256) % wordModulus + 32))
  expect "copy to fresh word" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence (.product .word .word) (Memory.mcopy (.var 1) (.var 0) (word 32) (word 0) (word 32))
        (withSize (Memory.mload (.var 1) (.var 0) (word 32))))))
    (.pair (scalar pattern) (scalar 64))
  expect "copy unwritten zero bytes" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence (.product .word .word) (Memory.mcopy (.var 1) (.var 0) (word 0) (word 64) (word 32))
        (withSize (Memory.mload (.var 1) (.var 0) (word 0))))))
    (.pair (scalar 0) (scalar 96))
  expect "zero copy ignores huge offsets" .word
    (memory (sequence .word (Memory.mcopy (.var 1) (.var 0) (word maximum) (word maximum) (word 0))
      (Memory.msize (.var 0)))) (scalar 0)
  let calldata := WordMapping.literal [(Word.zero, Word.ofNatModulo 0x12),
    (Word.ofNatModulo 1, Word.ofNatModulo 0x34)]
  expect "calldata copy pads absent bytes" (.product .word .word)
    (memory (sequence (.product .word .word)
      (Memory.copyFrom (.var 1) (.var 0) (word 1) calldata (word 0) (word 3))
      (withSize (Memory.mload (.var 1) (.var 0) (word 0)))))
    (.pair (scalar (0x1234 * 256 ^ 29)) (scalar 32))
  expect "calldata copy never wraps its source offset" .word
    (memory (sequence .word
      (Memory.copyFrom (.var 1) (.var 0) (word 0) calldata (word maximum) (word 3))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0)
  expect "calldata source range does not expand memory" .word
    (memory (sequence .word
      (Memory.copyFrom (.var 1) (.var 0) (word 0) calldata (word 4096) (word 1))
      (Memory.msize (.var 0)))) (scalar 32)
  let original := (List.range 96).map fun index => UInt8.ofNat (index * 7 + 3)
  let replacement := (List.range 32).map fun index => UInt8.ofNat (index * 3 + 1)
  for offset in List.range 32 do
    let expected := original.take offset ++ replacement ++ original.drop (offset + 32)
    let reads := LanguageResult.bind (.product .word .word)
      (Memory.mload (.var 1) (.var 0) (word 0))
      (LanguageResult.bind (.product .word .word)
        (Memory.mload (.var 2) (.var 1) (word 32))
        (LanguageResult.success (.pair (.var 1) (.var 0))))
    expect s!"packed unaligned write preserves both neighbors {offset}" (.product .word .word)
      (initialized original (sequence (.product .word .word)
        (Memory.mstore (.var 1) (.var 0) (word offset) (word (bytesWord replacement))) reads))
      (.pair (scalar (bytesWord expected)) (scalar (bytesWord (expected.drop 32))))
  for (destination, source) in [(1, 0), (0, 1), (31, 1), (1, 31)] do
    let expected := original.take destination ++ (original.drop source).take 65 ++
      original.drop (destination + 65)
    expect s!"packed bulk overlap {destination} {source}" .word
      (initialized original (sequence .word
        (Memory.mcopy (.var 1) (.var 0) (word destination) (word source) (word 65))
        (Memory.mload (.var 1) (.var 0) (word 64))))
      (scalar (bytesWord (expected.drop 64)))
  let rawOriginal := WordMapping.literal (original.zipIdx.map fun (byte, index) =>
    (Word.ofNatModulo index, Word.ofNatModulo byte.toNat))
  let packedOriginal := WordMapping.literal (Memory.packBytes original)
  for (label, copy, source) in [("raw", Memory.copyFrom, rawOriginal),
      ("packed", Memory.copyPackedFrom, packedOriginal)] do
    expect s!"{label} bulk copy with tail and padding" .word
      (memory (sequence .word (copy (.var 1) (.var 0) (word 1) source (word 65) (word 65))
        (Memory.mload (.var 1) (.var 0) (word 0))))
      (scalar (bytesWord (0 :: original.drop 65)))
  let edge := WordMapping.literal (Memory.packEntries
    [(Word.ofNatModulo maximum, Word.ofNatModulo 0xaa), (Word.zero, Word.ofNatModulo 0xbb)])
  expect "packed source word pads without wrapping" .word
    (Memory.readMemoryWord edge (word maximum)) (scalar (0xaa * 256 ^ 31))
  expect "packed copy crosses maximal source offset without wrapping" .word
    (memory (sequence .word
      (Memory.copyPackedFrom (.var 1) (.var 0) (word 0) edge (word maximum) (word 64))
      (Memory.mload (.var 1) (.var 0) (word 32)))) (scalar 0)
  let codeBytes := (List.range 1024).map fun index => UInt8.ofNat (index * 17 + 5)
  expect "packed kilobyte copy with unaligned destination" .word
    (memory (sequence .word
      (Memory.copyPackedFrom (.var 1) (.var 0) (word 3)
        (WordMapping.literal (Memory.packBytes codeBytes)) (word 0) (word 1024))
      (Memory.mload (.var 1) (.var 0) (word 995))))
    (scalar (bytesWord (codeBytes.drop 992)))
  let repeated := Memory.packEntries [(Word.zero, Word.ofNatModulo 0x123), (Word.zero, Word.ofNatModulo 0xab)]
  require (Memory.lookupByte repeated Word.zero == Word.ofNatModulo 0x23)
    "packing changed byte masking or first-entry precedence"
  require (Memory.lookupByte (Memory.packBytes [0xaa, 0xbb] maximum) Word.zero == Word.zero)
    "packing bytes wrapped an overflowing suffix"
  for offset in [maximum, wordModulus - 16, wordModulus - 32] do
    let program : Program := {
      resultType := .product (LanguageResult.resultType .unit) .word
      dataDefinitions := Memory.definitions
      body := memory (.pair (Memory.mstore (.var 1) (.var 0) (word offset) (word pattern))
        (.loadCell (.var 0)))
    }
    require program.check "overflow guard is ill-typed"
    match program.runStateful 10000 with
    | .done result store =>
        require (result == .pair (.inLeft .unit (.word Memory.overflowReason)) (scalar 0))
          "overflow wrapped the range or changed memory size"
        require (store[0]? == some (WordMapping.encode [])) "overflow changed byte memory"
    | other => throw (IO.userError s!"overflow did not terminate: {reprStr other}")

  let badCopy : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word
    dataDefinitions := Memory.definitions
    body := memory (.pair
      (Memory.mcopy (.var 1) (.var 0) (word 0) (word maximum) (word 32)) (.loadCell (.var 0)))
  }
  require badCopy.check "copy overflow guard is ill-typed"
  match badCopy.runStateful 10000 with
  | .done result store =>
      require (result == .pair (.inLeft .unit (.word Memory.overflowReason)) (scalar 0))
        "copy touched the destination before rejecting its source range"
      require (store[0]? == some (WordMapping.encode [])) "copy overflow changed byte memory"
  | other => throw (IO.userError s!"copy overflow did not terminate: {reprStr other}")

  let resumable : Program := {
    resultType := LanguageResult.resultType .word
    dataDefinitions := Memory.definitions
    body := memory (sequence .word (Memory.mstore (.var 1) (.var 0) (word 0) (word pattern))
      (sequence .word (Memory.mcopy (.var 1) (.var 0) (word 1) (word 0) (word 31))
        (Memory.mload (.var 1) (.var 0) (word 0))))
  }
  require resumable.check "resumable copy is ill-typed"
  match resumable.runStateful 10000 with
  | .outOfFuel checkpoint =>
      require (runStateful 3000000 checkpoint == resumable.runStateful 3010000)
        "resuming memory copy repeated or lost a byte write"
  | _ => throw (IO.userError "copy fixture did not suspend")

  -- Each raw input can have effects. Capturing them must neither repeat a
  -- reference expression nor read stale memory after evaluating the value.
  let tick (result : Expr) : Expr :=
    .letE (.storeCell (.var 2) (.binary .wordAdd (.loadCell (.var 2)) (word 1)))
      (result.weakenAt 0)
  let once : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word
    dataDefinitions := Memory.definitions
    body := .letE (.newCell .word (word 0))
      (memory (.pair (Memory.mstore8 (tick (.var 1)) (tick (.var 0)) (tick (word 0)) (tick (word 0xab)))
        (.loadCell (.var 2))))
  }
  require once.check "effectful memory arguments are ill-typed"
  match once.runStateful 100000 with
  | .done result store =>
      require (result == .pair (.inRight .word .unit) (scalar 4)) "memory argument effects were repeated"
      require (store[1]? == some (WordMapping.encode (Memory.packBytes [0xab])))
        "memory reference changed during argument capture"
  | other => throw (IO.userError s!"effectful memory arguments: {reprStr other}")

end Tests.RustHullMemory
end

section
-- leanmerge: from Solcore.Test.RustHullP256
set_option autoImplicit false
namespace Tests.RustHullP256
open Solcore.Core
open Solcore.Frontend.RustHull
open Lean (Json)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def ok (value : Value) : Value := .inRight .word value
private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {resultType := type, dataDefinitions := Memory.definitions, body}
  match inferDetailed [] [] body Memory.definitions with
  | .error error => throw (IO.userError s!"P256 {label}: invalid Core: {reprStr error}")
  | .ok actualType => require (actualType == type) s!"P256 {label}: wrong Core result type"
  match program.runStateful 10000000 with
  | .done actual _ =>
      require (actual == expected) s!"P256 {label}: expected {reprStr expected}, got {reprStr actual}"
  | .outOfFuel _ => throw (IO.userError s!"P256 {label}: test fuel exhausted")
  | .fault error _ => throw (IO.userError s!"P256 {label}: {reprStr error}")

private def verify (h r s x y : Nat) : Expr := P256.verify (word h) (word r) (word s) (word x) (word y)
private def check (label : String) (h r s x y : Nat) (valid : Bool) : IO Unit :=
  expect label (LanguageResult.resultType .bool) (verify h r s x y) (ok (.bool valid))

private def knownSignatures : IO Unit := do
  let h := 0xabcdef00112233445566778899aabbccddeeff00112233445566778899aabbcc
  let r := 0xa29295460e251beea1bdc9b84b2f3fe8e3a3e4d872baa3c55b78c9e448190ea9
  let s := 0x2d854575b092b3732d3d73c8414bda17f907776894cff2e8e25e733d200f3f5c
  let x := 0x6079df2480f92e4cf526c08e32ab82aed6599fddb777a039612fe7c9ef0247ba
  let y := 0xe2b4793e7c77585508c4780e4e53a36deefbb3548f4380ee6df04863cfc54c2d
  check "pinned upstream valid" h r s x y true
  check "pinned upstream changed hash" (h + 1) r s x y false
  check "high-s counterpart remains valid" h r (P256.order - s) x y true
  for (badR, badS) in [(0, s), (P256.order, s), (wordModulus - 1, s),
      (r, 0), (r, P256.order), (r, wordModulus - 1)] do
    check "scalar bounds" h badR badS x y false
  for (badX, badY) in [(P256.prime, y), (x, P256.prime), (wordModulus - 1, y),
      (x, wordModulus - 1), (0, 0), (x, (y + 1) % P256.prime)] do
    check "public-key bounds and membership" h r s badX badY false
  check "nonce-one key-one signature" 1 P256.generatorX (P256.generatorX + 1)
    P256.generatorX P256.generatorY true
  check "maximum hash reduction" (wordModulus - 1) P256.generatorX
    ((wordModulus - 1 + P256.generatorX) % P256.order) P256.generatorX P256.generatorY true
  check "reconstructed infinity is rejected" 1 1 1 P256.generatorX (P256.prime - P256.generatorY) false

private def curve : IO Unit := do
  let generator := Expr.pair (word P256.generatorX) (word P256.generatorY)
  let jacobian := Expr.pair (word P256.generatorX) (.pair (word P256.generatorY) (word 1))
  -- Independently derived by OpenSSL's P-256 key derivation for scalar 2.
  let doubledX := 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
  let doubledY := 0x07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1
  let expected := ok (.inRight .unit (.pair (scalar doubledX) (scalar doubledY)))
  let type := LanguageResult.resultType (P256.optionType P256.affineType)
  expect "double G" type (P256.normalize (P256.doublePoint jacobian)) expected
  expect "equal-point mixed addition" type (P256.normalize (P256.addAffine jacobian generator)) expected
  expect "opposite-point mixed addition" type
    (P256.normalize (P256.addAffine jacobian
      (.pair (word P256.generatorX) (word (P256.prime - P256.generatorY)))))
    (ok (.inLeft P256.affineType .unit))
  expect "joint G+G" type
    (LanguageResult.bind (P256.optionType P256.affineType)
      (P256.jointMultiply generator generator (word 1) (word 1)) (P256.normalize (.var 0))) expected

private def nibble (char : Char) : Except String Nat :=
  if '0' ≤ char && char ≤ '9' then .ok (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then .ok (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then .ok (char.toNat - 'A'.toNat + 10)
  else .error "invalid hexadecimal digit"
private def hexWord (chars : List Char) : Except String Nat :=
  chars.foldlM (fun value char => do return value * 16 + (← nibble char)) 0
private def get {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

/-- Maintained vectors select every distinct category from the EIP-7951
conformance set, including large reconstructed x, infinity, Shamir edge cases,
coordinate-zero points, malleability, and scalar bounds. -/
def referenceVectors (path : System.FilePath := "scripts/p256-vectors.json") : IO Unit := do
  let json ← get (Json.parse (← IO.FS.readFile path))
  let vectors ← get (json.getObjValAs? (List Json) "vectors")
  for vector in vectors do
    let name ← get (vector.getObjValAs? String "name")
    let input ← get (vector.getObjValAs? String "input")
    let valid ← get (vector.getObjValAs? Bool "valid")
    require (input.length == 320) s!"P256 reference {name}: input must contain five words"
    let words ← get ((List.range 5).mapM fun i => hexWord ((input.toList.drop (i * 64)).take 64))
    let [h, r, s, x, y] := words | throw (IO.userError "P256 reference word decoding failed")
    check name h r s x y valid

private def argumentsAndResume : IO Unit := do
  let tick (value : Nat) : Expr :=
    .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word value)
  let body := Expr.letE (.newCell .word (word 0))
    (.pair (P256.verify (tick 1) (tick P256.generatorX) (tick (P256.generatorX + 1))
      (tick P256.generatorX) (tick P256.generatorY)) (.loadCell (.var 0)))
  let expected := Value.pair (ok (.bool true)) (scalar 5)
  expect "all arguments once" (.product (LanguageResult.resultType .bool) .word) body expected
  match runStateful 2000 (.initial body) with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ => require (value == expected) "P256 resumption repeated inputs or changed the result"
      | _ => throw (IO.userError "P256 did not finish after resumption")
  | _ => throw (IO.userError "P256 resumption fixture did not suspend")

def run : IO Unit := do
  curve
  knownSignatures
  referenceVectors
  argumentsAndResume

end Tests.RustHullP256
end

section
-- leanmerge: from Solcore.Test.RustHullPrecompiles
set_option autoImplicit false
namespace Tests.RustHullPrecompiles
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def ok (value : Nat) : Value := .inRight .word (scalar value)
private def bytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def mappingEntries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then .ok [] else .error "wrong empty constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong cons constructor"
      return (key, value) :: (← mappingEntries tail)
  | _ => .error "malformed mapping value"

private structure Call where
  target : Nat
  gas : Nat := 1000000
  inputOffset : Nat := 0
  inputLength : Nat := 0
  outputOffset : Nat := 0
  outputLength : Nat := 0

private def invoke (call : Call) : Expr :=
  Precompiles.staticCall (.var 3) (.var 2) (.var 1) (.var 0)
    (number call.gas) (number call.target) (number call.inputOffset) (number call.inputLength)
    (number call.outputOffset) (number call.outputLength)

private def sequence : List Call → Expr
  | [] => LanguageResult.success (number 1)
  | [call] => invoke call
  | call :: rest => .letE (invoke call) ((sequence rest).weakenAt 0)

private def initialized (input : List UInt8) (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
    (.letE (.newCell .word (number 0))
      (.letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes [0xaa, 0xbb, 0xcc] 96)))
        (.letE (.newCell .word (number 99)) body)))

private def program (input : List UInt8) (calls : List Call) : Program := {
  resultType := LanguageResult.resultType .word
  dataDefinitions := Memory.definitions
  body := initialized input (sequence calls)
}

private def checkMapping (label : String) (actual : Option Value) (expected : List UInt8) : IO Unit := do
  let some actual := actual | throw (IO.userError s!"{label}: missing mapping cell")
  let entries ← match mappingEntries actual with
    | .ok entries => pure entries
    | .error error => throw (IO.userError s!"{label}: {error}")
  let expected := Memory.packBytes expected
  for (key, _) in entries ++ expected do
    require (WordMapping.lookupEntries key entries == WordMapping.lookupEntries key expected)
      s!"{label}: incorrect packed word {key.val}"

private def checkResult (label : String) (expected : Value) (expectedMemory expectedReturn : List UInt8)
    (expectedSize : Nat) (result : StatefulRunResult) : IO Unit := do
  match result with
  | .done value store =>
      require (value == expected) s!"{label}: incorrect result {reprStr value}"
      checkMapping s!"{label} memory" store[0]? expectedMemory
      require (store[1]? == some (scalar expectedSize)) s!"{label}: incorrect memory size"
      checkMapping s!"{label} returndata" store[2]? expectedReturn
      require (store[3]? == some (scalar expectedReturn.length)) s!"{label}: incorrect returndata size"
  | .outOfFuel _ => throw (IO.userError s!"{label}: test fuel exhausted")
  | .fault fault _ => throw (IO.userError s!"{label}: {reprStr fault}")

private def check (label : String) (input : List UInt8) (calls : List Call) (expected : Value)
    (expectedMemory expectedReturn : List UInt8) (expectedSize : Nat) (resume : Bool := false) : IO Unit := do
  let compiled := program input calls
  match inferDetailed [] [] compiled.body Memory.definitions with
  | .error error => throw (IO.userError s!"{label}: invalid Core: {reprStr error}")
  | .ok type => require (type == compiled.resultType) s!"{label}: incorrect Core result type"
  checkResult label expected expectedMemory expectedReturn expectedSize (compiled.runStateful 20000000)
  if resume then
    match compiled.runStateful 2000 with
    | .outOfFuel state =>
        checkResult s!"{label} resumed" expected expectedMemory expectedReturn expectedSize
          (runStateful 20000000 state)
    | _ => throw (IO.userError s!"{label}: resumption fixture did not suspend")

private def overwritten (input : List UInt8) (offset : Nat) (replacement : List UInt8) : List UInt8 :=
  let padded := input ++ List.replicate (offset + replacement.length - input.length) 0
  padded.take offset ++ replacement ++ padded.drop (offset + replacement.length)

private def identityTests : IO Unit := do
  let input := (List.range 160).map fun i => UInt8.ofNat (i * 7 + 3)
  for (source, destination, length, outputLength) in [(0, 1, 65, 65), (1, 0, 65, 65),
      (7, 31, 65, 17), (7, 31, 33, 65), (7, 31, 33, 0)] do
    let output := (input.drop source).take length
    check s!"identity overlapping output {source} {destination} {length} {outputLength}" input
      [{target := 4, inputOffset := source, inputLength := length,
        outputOffset := destination, outputLength}]
      (ok 1) (overwritten input destination (output.take outputLength)) output
      (((max (source + length) (if outputLength = 0 then 0 else destination + outputLength) + 31) / 32) * 32)
      (source == 0 && destination == 1)
  for length in [0, 1, 31, 32, 33, 64, 65] do
    let gas := 15 + 3 * ((length + 31) / 32)
    let size := ((length + 31) / 32) * 32
    check s!"identity exact gas {length}" input [{target := 4, gas, inputLength := length}]
      (ok 1) input (input.take length) size
    check s!"identity insufficient gas {length}" input [{target := 4, gas := gas - 1, inputLength := length}]
      (ok 0) input [] size
  check "identity ignores target high bits" input [{target := 2 ^ 200 + 4, inputLength := 3}]
    (ok 1) input (input.take 3) 32
  check "empty identity ignores enormous offsets" input
    [{target := 4, gas := 15, inputOffset := wordModulus - 1, outputOffset := wordModulus - 1}]
    (ok 1) input [] 0
  check "identity copies missing input as zero" [0xaa]
    [{target := 4, inputLength := 4, outputOffset := 8, outputLength := 4}]
    (ok 1) [0xaa, 0, 0, 0, 0, 0, 0, 0, 0xaa, 0, 0, 0] [0xaa, 0, 0, 0] 32

private def hashTests : IO Unit := do
  let input := "abc".toUTF8.toList ++ List.replicate 64 0xee
  for (target, base, cost, digest, empty) in
      [(2, 60, 12, 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad,
        0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855),
       (3, 600, 120, 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc,
        0x9c1185a5c5e9fc54612808977ee8f548b2258d31)] do
    check s!"hash {target} exact gas, overlapping unaligned output, dirty suffix" input
      [{target, gas := base + cost, inputLength := 3, outputOffset := 1, outputLength := 40}]
      (ok 1) (overwritten input 1 (bytes digest)) (bytes digest) 64 true
    check s!"hash {target} truncated output retains complete return data" input
      [{target, inputLength := 3, outputOffset := 31, outputLength := 7}]
      (ok 1) (overwritten input 31 ((bytes digest).take 7)) (bytes digest) 64
    check s!"hash {target} no output still retains digest" input
      [{target, inputLength := 3, outputOffset := wordModulus - 1}]
      (ok 1) input (bytes digest) 32
    check s!"hash {target} gas failure preserves output" input
      [{target, gas := base + cost - 1, inputLength := 3, outputOffset := 1, outputLength := 40}]
      (ok 0) input [] 64
    check s!"hash {target} empty input at maximal offset" input
      [{target, gas := base, inputOffset := wordModulus - 1}]
      (ok 1) input (bytes empty) 0
    -- The input range is valid but its required gas is far beyond practical
    -- execution. RIPEMD's mathematical gas cost also exceeds 2^256 here.
    check s!"hash {target} enormous cost does not wrap" []
      [{target, gas := if target = 3 then wordModulus - 1 else 0,
        inputLength := wordModulus - 32}]
      (ok 0) [] [] (wordModulus - 32)

private def recoveryTests : IO Unit := do
  let hash := 0xaabbccddeeff00112233445566778899aabbccddeeff00112233445566778899
  let r := 0xb3ba6dd3757d18f28736e84b1296af85362b7bdf4548710733c6325abf95311d
  let s := 0x3523e7d34da277c59af090e44cebddb10b73be11780f028d02cf5ae5f24109fc
  let address := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
  let input := [0xaa] ++ bytes hash ++ bytes 27 ++ bytes r ++ bytes s ++ List.replicate 64 0xee
  check "recovery valid, unaligned input and overlapping output" input
    [{target := 1, gas := 3000, inputOffset := 1, inputLength := 128,
      outputOffset := 7, outputLength := 64}]
    (ok 1) (overwritten input 7 (bytes address)) (bytes address) 160 true
  check "recovery ignores excess input" input
    [{target := 1, inputOffset := 1, inputLength := 160}]
    (ok 1) input (bytes address) 192
  check "recovery gas failure preserves output" input
    [{target := 1, gas := 2999, inputOffset := 1, inputLength := 128,
      outputOffset := 0, outputLength := 32}]
    (ok 0) input [] 160
  -- Private key one and nonce one give s = r + h. Choosing h=104 makes
  -- s's last byte zero. A dirty 128th byte must be excluded by length=127.
  let partialInput := bytes 104 ++ bytes 27 ++ bytes Secp256k1.generatorX ++
    (bytes (Secp256k1.generatorX + 104)).take 31 ++ [0xee]
  check "recovery masks the partially supplied final word" partialInput
    [{target := 1, gas := 3000, inputLength := 127, outputLength := 32}]
    (ok 1) (overwritten partialInput 0 (bytes address)) (bytes address) 128
  for length in [0, 31, 32, 33, 63, 64, 65, 95, 96] do
    check s!"recovery short input ignores dirty suffix {length}" input
      [{target := 1, inputOffset := 1, inputLength := length, outputOffset := 0, outputLength := 32}]
      (ok 1) input [] (((max (if length = 0 then 0 else length + 1) 32 + 31) / 32) * 32)
  for v in [1, 29, 283] do
    let invalid := bytes hash ++ bytes v ++ bytes r ++ bytes s
    check s!"invalid v {v} returns success with empty output" invalid
      [{target := 1, inputLength := 128, outputLength := 32}]
      (ok 1) invalid [] 128
  check "invalid recovery clears previous return data" input
    [{target := 1, inputOffset := 1, inputLength := 128},
     {target := 1, inputOffset := 1, inputLength := 64}]
    (ok 1) input [] 160
  check "insufficient gas clears previous return data" input
    [{target := 4, inputLength := 65}, {target := 1, gas := 2999, inputLength := 128}]
    (ok 0) input [] 128
  check "short identity replaces previous longer return data" input
    [{target := 4, inputLength := 65}, {target := 4, inputOffset := 3, inputLength := 7}]
    (ok 1) input ((input.drop 3).take 7) 96

private def p256Tests : IO Unit := do
  let signature := bytes 1 ++ bytes P256.generatorX ++ bytes (P256.generatorX + 1) ++
    bytes P256.generatorX ++ bytes P256.generatorY
  let input := [0xaa] ++ signature ++ List.replicate 32 0xee
  check "P256 valid unaligned input and overlapping clipped output" input
    [{target := 0x100, gas := 6900, inputOffset := 1, inputLength := 160,
      outputOffset := 7, outputLength := 40}]
    (ok 1) (overwritten input 7 (bytes 1)) (bytes 1) 192 true
  check "P256 no output retains complete return data" input
    [{target := 0x100, gas := 6900, inputOffset := 1, inputLength := 160}]
    (ok 1) input (bytes 1) 192
  for length in [0, 1, 32, 128, 159, 161, 192] do
    check s!"P256 requires exactly 160 bytes, length {length}" input
      [{target := 0x100, gas := 6900, inputOffset := 1, inputLength := length, outputLength := 32}]
      (ok 1) input [] (((max 32 (if length = 0 then 0 else length + 1) + 31) / 32) * 32)
  check "P256 uses EIP-7951 cost rather than RIP-7212 cost" input
    [{target := 0x100, gas := 3450, inputOffset := 1, inputLength := 160, outputLength := 32}]
    (ok 0) input [] 192
  check "P256 one gas short" input
    [{target := 0x100, gas := 6899, inputOffset := 1, inputLength := 160, outputLength := 32}]
    (ok 0) input [] 192
  let invalid := bytes 2 ++ signature.drop 32
  check "P256 invalid signature preserves output and clears previous return data" invalid
    [{target := 4, inputLength := 65}, {target := 0x100, gas := 6900, inputLength := 160, outputLength := 32}]
    (ok 1) invalid [] 160

private def boundaries : IO Unit := do
  check "unsupported target is an explicit language failure" [0xaa]
    [{target := 5, inputLength := 1, outputLength := 1}]
    (.inLeft .word (.word Precompiles.unsupportedTargetReason)) [0xaa] [] 32
  -- A rejected range fails before dispatch. Its pre-existing return data has
  -- not been cleared because no call was started.
  let bad := program [0xaa] [{target := 4, inputOffset := wordModulus - 1, inputLength := 1}]
  require bad.check "overflow program is ill-typed"
  match bad.runStateful 10000 with
  | .done value store =>
      require (value == .inLeft .word (.word Memory.overflowReason)) "input overflow did not fail"
      require (store[1]? == some (scalar 0)) "input overflow expanded memory"
      require (store[3]? == some (scalar 99)) "input overflow started the call"
      checkMapping "input overflow unchanged memory" store[0]? [0xaa]
  | other => throw (IO.userError s!"input overflow: {reprStr other}")
  let badOutput := program [0xaa]
    [{target := 4, inputLength := 1, outputOffset := wordModulus - 16, outputLength := 32}]
  require badOutput.check "output overflow program is ill-typed"
  match badOutput.runStateful 10000 with
  | .done value store =>
      require (value == .inLeft .word (.word Memory.overflowReason)) "output overflow did not fail"
      require (store[3]? == some (scalar 99)) "output overflow started the call"
      checkMapping "output overflow unchanged memory" store[0]? [0xaa]
  | other => throw (IO.userError s!"output overflow: {reprStr other}")

private def argumentsOnce : IO Unit := do
  -- After the four runtime cells, a separate counter records evaluation of
  -- both reference arguments and scalar arguments, including after resuming.
  let tick (value : Expr) : Expr :=
    .letE (.storeCell (.var 4) (.binary .wordAdd (.loadCell (.var 4)) (number 1))) (value.weakenAt 0)
  let call := Precompiles.staticCall (tick (.var 3)) (tick (.var 2)) (tick (.var 1)) (tick (.var 0))
    (tick (number 18)) (tick (number 4)) (tick (number 0)) (tick (number 3))
    (tick (number 1)) (tick (number 3))
  let compiled : Program := {
    resultType := .product (LanguageResult.resultType .word) .word
    dataDefinitions := Memory.definitions
    body := .letE (.newCell .word (number 0))
      (initialized "abc".toUTF8.toList (.pair call (.loadCell (.var 4))))
  }
  require compiled.check "effectful precompile arguments are ill-typed"
  for fuel in [50, 2000] do
    match compiled.runStateful fuel with
    | .outOfFuel state =>
        match runStateful 2000000 state with
        | .done result store =>
            require (result == .pair (ok 1) (scalar 10)) "precompile arguments repeated or skipped"
            checkMapping "effectful precompile overlap" store[1]? "aabc".toUTF8.toList
        | other => throw (IO.userError s!"effectful precompile resume: {reprStr other}")
    | _ => throw (IO.userError "effectful precompile fixture did not suspend")

def run : IO Unit := do
  identityTests
  hashTests
  recoveryTests
  p256Tests
  boundaries
  argumentsOnce

end Tests.RustHullPrecompiles
end

section
-- leanmerge: from Solcore.Test.RustHullSecp256k1
set_option autoImplicit false
namespace Tests.RustHullSecp256k1
open Solcore.Core
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (n : Nat) : Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def generator : Expr := .pair (word Secp256k1.generatorX) (word Secp256k1.generatorY)
private def jacobian : Expr := .pair (word Secp256k1.generatorX) (.pair (word Secp256k1.generatorY) (word 1))
private def ok (value : Value) : Value := .inRight .word value
private def someValue (value : Value) : Value := .inRight .unit value
private def absent (type : Ty) : Value := .inLeft type .unit

private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {resultType := type, dataDefinitions := Memory.definitions, body}
  match inferDetailed [] [] body Memory.definitions with
  | .error error => throw (IO.userError s!"secp256k1 {label}: invalid Core: {reprStr error}")
  | .ok actualType => require (actualType == type) s!"secp256k1 {label}: wrong Core result type"
  match program.runStateful 10000000 with
  | .done actual _ => do
    require (actual == expected) s!"secp256k1 {label}: expected {reprStr expected}, got {reprStr actual}"
  | .outOfFuel _ => throw (IO.userError s!"secp256k1 {label}: test fuel exhausted")
  | .fault error _ => throw (IO.userError s!"secp256k1 {label}: {reprStr error}")

private def recover (h v r s : Nat) : Expr := Secp256k1.recover (word h) (word v) (word r) (word s)
private def optionWord : Ty := LanguageResult.resultType (Secp256k1.optionType .word)

private def fieldAndCurve : IO Unit := do
  for (a, e, m, result) in [(2, 10, 17, 4), (5, 0, 1, 0), (5, 0, 0, 0), (0, 0, 17, 1)] do
    expect "modular power" (LanguageResult.resultType .word)
      (Secp256k1.powMod (word a) (word e) (word m)) (ok (scalar result))
  expect "field inverse" (LanguageResult.resultType .word)
    (Secp256k1.powMod (word 2) (word (Secp256k1.prime - 2)) (word Secp256k1.prime))
    (ok (scalar ((Secp256k1.prime + 1) / 2)))
  let doubledX := 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
  let doubledY := 0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a
  let expected := ok (someValue (.pair (scalar doubledX) (scalar doubledY)))
  let optionAffine := LanguageResult.resultType (Secp256k1.optionType Secp256k1.affineType)
  expect "double generator" optionAffine (Secp256k1.normalize (Secp256k1.doublePoint jacobian)) expected
  expect "equal-point mixed addition" optionAffine (Secp256k1.normalize (Secp256k1.addAffine jacobian generator)) expected
  expect "opposite-point mixed addition" optionAffine
    (Secp256k1.normalize (Secp256k1.addAffine jacobian
      (.pair (word Secp256k1.generatorX) (word (Secp256k1.prime - Secp256k1.generatorY)))))
    (ok (absent Secp256k1.affineType))
  expect "joint scalar multiplication" optionAffine
    (LanguageResult.bind (Secp256k1.optionType Secp256k1.affineType)
      (Secp256k1.jointMultiply generator generator (word 1) (word 1))
      (Secp256k1.normalize (.var 0))) expected

private def recovery : IO Unit := do
  -- Pinned upstream tests/e2e/ecrecover/main.sol, private key one.
  let hash := 0xaabbccddeeff00112233445566778899aabbccddeeff00112233445566778899
  let r := 0xb3ba6dd3757d18f28736e84b1296af85362b7bdf4548710733c6325abf95311d
  let s := 0x3523e7d34da277c59af090e44cebddb10b73be11780f028d02cf5ae5f24109fc
  let address := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
  expect "upstream valid recovery" optionWord (recover hash 27 r s) (ok (someValue (scalar address)))
  expect "high-s parity counterpart" optionWord (recover hash 28 r (Secp256k1.order - s))
    (ok (someValue (scalar address)))
  for (v, invalidR, invalidS) in [(1, r, s), (29, r, s), (283, r, s),
      (27, 0, s), (27, Secp256k1.order, s), (27, r, 0), (27, r, Secp256k1.order)] do
    expect "invalid signature components" optionWord (recover hash v invalidR invalidS)
      (ok (absent .word))
  expect "nonce-one signature" optionWord
    (recover 1 27 Secp256k1.generatorX (Secp256k1.generatorX + 1))
    (ok (someValue (scalar address)))
  expect "nonsquare recovery coordinate" optionWord (recover 1 27 5 1) (ok (absent .word))
  -- Independently checked against Anvil's precompile; vectors are retained in
  -- scripts/secp256k1-vectors.json. These cover both parities and hash reduction.
  expect "maximum hash, key two" optionWord
    (recover (wordModulus - 1) 28
      0x270c504ade45b9bf70ed7dd54f2f253671c4568e3b2a2319d2efc6942b58f796
      0x076b9b8b0449bc498635d324e2f50365964e65ef0fcbcec9b9941e69f91b0aaa)
    (ok (someValue (scalar 0x2b5ad5c4795c026514f8317c7a215e218dccd6cf)))
  expect "zero hash, key three" optionWord
    (recover 0 27
      0xe95058f48325b8b37415edd898822fcfc83d8fdc5e257d3c370c0304c42dd5f2
      0x6836450f27b3ccd9d0e86629627b28b61fcdaeab49d9099f4170ccd3b3258e81)
    (ok (someValue (scalar 0x6813eb9362372eef6200f3b1dbc3f819671cba69)))
  expect "infinite recovered point" optionWord (recover 1 27 Secp256k1.generatorX 1)
    (ok (absent .word))

private def resumptionAndArguments : IO Unit := do
  let address := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf
  let tick (value : Nat) : Expr :=
    .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (word 1))) (word value)
  let body := Expr.letE (.newCell .word (word 0))
    (.letE (Secp256k1.recover (tick 1) (tick 27)
      (tick Secp256k1.generatorX) (tick (Secp256k1.generatorX + 1)))
      (.pair (.var 0) (.loadCell (.var 1))))
  let expected := Value.pair (ok (someValue (scalar address))) (scalar 4)
  expect "arguments evaluated once; caller cell preserved"
    (.product optionWord .word) body expected
  match runStateful 2000 (.initial body) with
  | .outOfFuel state =>
      match runStateful 10000000 state with
      | .done value _ => require (value == expected) "recovery resumption repeated arguments or changed the address"
      | _ => throw (IO.userError "recovery did not finish after resumption")
  | _ => throw (IO.userError "recovery suspension fixture did not exhaust its initial fuel")

def run : IO Unit := do
  fieldAndCurve
  recovery
  resumptionAndArguments

end Tests.RustHullSecp256k1
end

section
-- leanmerge: from Solcore.Test.RustYulPrimitives
set_option autoImplicit false

namespace Tests.RustYulPrimitives

open Solcore.Core
open Solcore.Frontend.RustYulPrimitives

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def lower (name : String) (arguments : List Expr) : IO Lowered :=
  match compile name arguments with
  | .ok lowered => pure lowered
  | .error error => throw (IO.userError s!"Yul {name}: {reprStr error}")

private def word (value : Int) : Word := Word.ofIntModulo value
private def literal (value : Int) : Expr := .word (word value)

private def fails (name : String) (arguments : List Expr) (expected : Error) : Bool :=
  match compile name arguments with
  | .error error => error == expected
  | .ok _ => false

private def checkWord (name : String) (arguments : List Int) (expected : Int) : IO Unit := do
  let lowered ← lower name (arguments.map literal)
  let program : Program := ⟨lowered.type, lowered.expression, []⟩
  require program.check s!"Yul {name}: invalid generated Core type"
  require (program.run 500 == .done (.word (word expected)))
    s!"Yul {name}{reprStr arguments}: expected {expected}, got {reprStr (program.run 500)}"

private def tick : Expr :=
  .letE (.loadCell (.var 0))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.var 0) (literal 1))) (.var 1))

def run : IO Unit := do
  let maximum : Int := 2 ^ 256 - 1
  let minimum : Int := -(2 ^ 255)
  for (name, arguments, expected) in [
      ("add", [maximum, 1], 0), ("sub", [7, 11], -4), ("mul", [7, 9], 63),
      ("div", [17, 5], 3), ("div", [17, 0], 0),
      ("mod", [17, 5], 2), ("mod", [17, 0], 0),
      ("sdiv", [-7, 2], -3), ("sdiv", [minimum, -1], minimum), ("sdiv", [-7, 0], 0),
      ("smod", [-7, 2], -1), ("smod", [7, -2], 1), ("smod", [-7, 0], 0),
      ("exp", [2, 256], 0), ("exp", [0, 0], 1),
      ("signextend", [0, 128], -128), ("signextend", [32, 128], 128),
      ("lt", [1, 2], 1), ("lt", [2, 1], 0), ("lt", [-1, 0], 0),
      ("gt", [2, 1], 1), ("gt", [2, 2], 0),
      ("slt", [-1, 0], 1), ("slt", [0, -1], 0),
      ("sgt", [0, -1], 1), ("sgt", [-1, 0], 0),
      ("eq", [5, 5], 1), ("eq", [5, 6], 0),
      ("iszero", [0], 1), ("iszero", [256], 0),
      ("and", [12, 10], 8), ("or", [12, 10], 14), ("xor", [12, 10], 6),
      ("not", [0], -1), ("byte", [0, 171 * 2 ^ 248], 171), ("byte", [32, -1], 0),
      ("shl", [3, 5], 40), ("shl", [256, 1], 0),
      ("shr", [3, 40], 5), ("shr", [256, -1], 0),
      ("sar", [1, -3], -2), ("sar", [256, -1], -1),
      ("clz", [0], 256), ("clz", [1], 255), ("clz", [2 ^ 255], 0),
      ("addmod", [maximum, 1, 3], 1), ("addmod", [1, 2, 0], 0),
      ("mulmod", [2 ^ 255, 2, 3], 1), ("mulmod", [1, 2, 0], 0)] do
    checkWord name arguments expected

  let popped ← lower "pop" [literal 7]
  let popProgram : Program := ⟨popped.type, popped.expression, []⟩
  require (popProgram.check && popProgram.run 100 == .done .unit)
    "Yul pop did not consume a word and return unit"
  let invalidPop ← lower "pop" [.bool true]
  require (!(Program.mk invalidPop.type invalidPop.expression []).check)
    "Yul pop silently accepted a Boolean argument"
  let invalidAdd ← lower "add" [.bool true, literal 1]
  require (!(Program.mk invalidAdd.type invalidAdd.expression []).check)
    "Yul add silently accepted a Boolean argument"
  require (fails "add" [literal 1] (.wrongArity "add" 2 1))
    "Yul add accepted missing arguments"
  require (fails "clz" [literal 1, literal 2] (.wrongArity "clz" 1 2))
    "Yul clz accepted extra arguments"
  for name in ["sload", "mstore", "keccak256", "return", "call", "missing"] do
    require (!supports name && fails name [] (.unknownBuiltin name))
      s!"Yul pure lowering silently accepted effect {name}"

  let ordered ← lower "sub" [tick, tick]
  let orderedProgram : Program := {
    resultType := .product .word .word
    body := .letE (.newCell .word (literal 0))
      (.pair ordered.expression (.loadCell (.var 0)))
  }
  require orderedProgram.check "effectful Yul argument lowering is ill-typed"
  let orderedExpected : StatefulRunResult :=
    .done (.pair (.word (word 1)) (.word (word 2))) [.word (word 2)]
  require (orderedProgram.runStateful 500 == orderedExpected)
    "Yul arguments were not evaluated once each, right to left"
  match orderedProgram.runStateful 10 with
  | .outOfFuel state =>
      require (runStateful 500 state == orderedExpected)
        "resuming a Yul argument computation repeated or lost an effect"
  | _ => throw (IO.userError "Yul resumption fixture did not suspend")

  let ternary ← lower "addmod" [tick, tick, tick]
  let ternaryProgram : Program := {
    resultType := .product .word .word
    body := .letE (.newCell .word (literal 5))
      (.pair ternary.expression (.loadCell (.var 0)))
  }
  require (ternaryProgram.check && ternaryProgram.runStateful 500 ==
      .done (.pair (.word (word 3)) (.word (word 8))) [.word (word 8)])
    "Yul ternary argument positions or right-to-left effects changed"

  let discarded ← lower "pop" [tick]
  let discardedProgram : Program := {
    resultType := .product .unit .word
    body := .letE (.newCell .word (literal 0))
      (.pair discarded.expression (.loadCell (.var 0)))
  }
  require (discardedProgram.check && discardedProgram.run 500 ==
      .done (.pair .unit (.word (word 1))))
    "Yul pop discarded the argument's effects"

  let firstFault ← lower "sub" [.var 98, .var 99]
  require ((Program.mk firstFault.type firstFault.expression []).run 100 ==
      .fault (.unboundVariable 99))
    "Yul evaluated the left argument before a failing right argument"

end Tests.RustYulPrimitives
end
