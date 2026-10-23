import Solcore.Frontend.RustHull.Creation
import Solcore.Abi.Keccak256
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullCreation
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def ok (value : Nat) : Value := .inRight .word (scalar value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat

private def execute (label : String) (compiled : Program) (expected : Value) : IO Store := do
  require compiled.check s!"{label}: ill-typed creation Core"
  match compiled.runStateful 10000000 with
  | .done value store =>
      require (value == expected) s!"{label}: {reprStr value}"
      pure store
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def addressProgram (creator nonce : Nat) : Program := {
  resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
  body := Creation.createAddress (number creator) (number nonce)}

private def address2Program (input : List UInt8) (creator salt offset length : Nat) : Program := {
  resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
  body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
    (.letE (.newCell .word (number 0))
      (Creation.create2Address (.var 1) (.var 0) (number creator) (number salt) (number offset) (number length)))}

private def digest (input : List UInt8) : Nat :=
  (Solcore.Abi.V1.Keccak256.hash input.toByteArray).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0
private def wordBytes (length value : Nat) : List UInt8 :=
  (List.range length).map fun index => UInt8.ofNat (value / 256 ^ (length - 1 - index) % 256)
private def expectedAddress2 (creator salt : Nat) (input : List UInt8) : Nat :=
  digest (bytes [255] ++ wordBytes 20 creator ++ wordBytes 32 salt ++ wordBytes 32 (digest input)) % 2 ^ 160

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "creation resume budget exhausted")
  | attempts + 1, state => match runStateful 5000 state with
      | .outOfFuel state => resumeChunks attempts state
      | result => pure result

private def addressTests : IO Unit := do
  -- Independent cast compute-address and RLP/Keccak vectors are recorded in
  -- Tests/Fixtures/EvmAccounts/address-vectors.json.
  let creator := 0xdeadbeef * 2 ^ 128
  for (nonce, expected) in [
      (0, 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea),
      (1, 0x054dd934335ea61232ae4c051f8bf20e540f8291),
      (127, 0x7feb088e1893d4a1087288d386c07252abb3c02e),
      (128, 0x2297787b25b800d655071345a1d3a7951404b50c),
      (255, 0xc8d17a8bdb6001525f8594e3ca4413d4bd644605),
      (256, 0xa0ddf5980551b5ec83721bcf168785ac3cedb183),
      (2 ^ 64 - 1, 0x66e93872e94cc56d1da3bb63f81dabd9c1d6c125)] do
    let _ ← execute s!"CREATE nonce {nonce}" (addressProgram creator nonce) (ok expected)
  let _ ← execute "CREATE ignores creator high bits" (addressProgram (creator + 2 ^ 200) 0)
    (ok 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea)
  for (address, salt, input, expected) in [
      (0, 0, bytes [0], 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38),
      (creator, 0, bytes [0], 0xb928f69bb1d91cd65274e3c79d8986362984fda3),
      (creator, 22207167547627365064083290255604625247830016, bytes [0],
        0xf2a2934e8506d97a2cee99962533f9729676ae24),
      (0xdeadbeef, 0xcafebabe, bytes [0xde, 0xad, 0xbe, 0xef],
        0x60f3f640a8508fc6a86d45df051962668e1e8ac7)] do
    let store ← execute "CREATE2 independent vector"
      (address2Program input address salt 0 input.length) (ok expected)
    require (store[0]? == some (WordMapping.encode (Memory.packBytes input)))
      "CREATE2 derivation changed caller memory"
    require (store[1]? == some (scalar 32)) "CREATE2 input range did not expand memory"
  let input := (List.range 147).map fun index => UInt8.ofNat (index * 19 + 5)
  let expected := expectedAddress2 creator (wordModulus - 1) ((input.drop 7).take 137)
  let compiled := address2Program input (creator + 2 ^ 200) (wordModulus - 1) 7 137
  let store ← execute "CREATE2 unaligned multi-block init" compiled (ok expected)
  require (store[0]? == some (WordMapping.encode (Memory.packBytes input)) &&
    store[1]? == some (scalar 160)) "CREATE2 scratch memory escaped into caller memory"
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint => match ← resumeChunks 1000 checkpoint with
      | .done value _ => require (value == ok expected) "CREATE2 address changed across resumes"
      | other => throw (IO.userError s!"CREATE2 resume: {reprStr other}")
  | _ => throw (IO.userError "CREATE2 address test did not suspend")
  let store ← execute "CREATE2 empty init ignores maximal offset"
    (address2Program input creator 0 (wordModulus - 1) 0) (ok (expectedAddress2 creator 0 []))
  require (store[1]? == some (scalar 0)) "empty init expanded caller memory"
  let _ ← execute "CREATE2 range overflow remains a language failure"
    (address2Program [] creator 0 (wordModulus - 16) 32)
    (.inLeft .word (.word Memory.overflowReason))
  pure ()

private structure Invocation where
  depth : Nat := 0
  offset : Nat := 7
  length : Nat := 65
  create2 : Bool := false
  installed : Bool := true
  address : Nat := 0x1234
  fail : Bool := false
  mutate : Bool := false
  tick : Bool := false

private def callbackBody (invocation : Invocation) : Expr :=
  let request := Expr.var 0
  let rejected := LanguageResult.failure Creation.responseType (number 99)
  let result := if invocation.fail then rejected else LanguageResult.success
    (Creation.response (number invocation.address)
      (Creation.requestField 6 request) (Creation.requestField 7 request))
  let result := if invocation.mutate then LocalSequence.discard Creation.responseType
    (Memory.mstore8 (.var 6) (.var 5) (number 7) (number 0xee)) result else result
  let checks := [(0, 0xabc), (1, 17), (2, 77), (4, invocation.depth + 1), (5, 88), (7, invocation.length)]
  let checked : Expr := checks.foldr (fun (index, expected) next =>
    .ifE (.binary .wordEq (Creation.requestField index request) (number expected)) next rejected)
    (.ifE (Creation.requestField 3 request) (if invocation.create2 then result else rejected)
      (if invocation.create2 then rejected else result))
  .letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (number 1))) (checked.weakenAt 0)

private def invoke (invocation : Invocation) : Expr :=
  let tick (value : Expr) := if invocation.tick then
    Expr.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1)))
      (value.weakenAt 0) else value
  Creation.invoke (tick (.var 5)) (tick (.var 4)) (tick (.var 3)) (tick (.var 2)) (tick (.var 1))
    (tick (number (2 ^ 200 + 0xabc))) (tick (number invocation.depth))
    (tick (number 17)) (tick (number 77)) (tick (.bool invocation.create2)) (tick (number 88))
    (tick (number invocation.offset)) (tick (number invocation.length))

private def program (input : List UInt8) (invocation : Invocation) : Program :=
  let body := if invocation.installed then
    Expr.letE (.storeCell (.var 1) (.inRight .unit
      (.lambda Creation.requestType (LanguageResult.resultType Creation.responseType) (callbackBody invocation))))
      ((invoke invocation).weakenAt 0) else invoke invocation
  {resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
   body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
     (.letE (.newCell .word (number 0))
       (.letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes (bytes [0xaa, 0xbb]))))
         (.letE (.newCell .word (number 2))
           (.letE (OptionalCell.allocate Creation.callbackType)
             (.letE (.newCell .word (number 0)) body)))))}

private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "invalid empty map"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "invalid map constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid map value"

private def verify (label : String) (input returned : List UInt8) (size count : Nat) (store : Store) : IO Unit := do
  require (store[0]? == some (WordMapping.encode (Memory.packBytes input))) s!"{label}: memory changed"
  require (store[1]? == some (scalar size)) s!"{label}: memory extent"
  let some mapping := store[2]? | throw (IO.userError s!"{label}: missing return data cell")
  let actual ← match entries mapping with
    | .ok actual => pure actual
    | .error error => throw (IO.userError s!"{label}: {error}")
  let expected := Memory.packBytes returned
  for (key, _) in actual ++ expected do
    require (WordMapping.lookupEntries key actual == WordMapping.lookupEntries key expected)
      s!"{label}: return bytes at packed word {key.val}"
  require (store[3]? == some (scalar returned.length)) s!"{label}: return-data extent"
  require (store[5]? == some (scalar count)) s!"{label}: argument/callback count"

private def transportTests : IO Unit := do
  let input := (List.range 160).map fun index => UInt8.ofNat (index * 7 + 3)
  let payload := (input.drop 7).take 65
  for create2 in [false, true] do
    let compiled := program input {create2, tick := true}
    let store ← execute "CREATE transport fields and exact-once arguments" compiled (ok 0x1234)
    verify "CREATE transport fields and exact-once arguments" input payload 96 14 store
  let compiled := program input {address := 0, mutate := true}
  let store ← execute "CREATE revert bytes preserve input snapshot" compiled (ok 0)
  let changed := input.take 7 ++ bytes [0xee] ++ input.drop 8
  verify "CREATE revert bytes preserve input snapshot" changed payload 96 1 store
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint => match ← resumeChunks 1000 checkpoint with
      | .done value store =>
          require (value == ok 0) "creation transport resume changed result"
          verify "creation transport resume" changed payload 96 1 store
      | other => throw (IO.userError s!"creation transport resume: {reprStr other}")
  | _ => throw (IO.userError "creation transport did not suspend")
  let store ← execute "depth1023 allows child1024" (program input {depth := 1023}) (ok 0x1234)
  verify "depth1023 allows child1024" input payload 96 1 store
  for depth in [1024, wordModulus - 1] do
    let store ← execute "depth refusal clears return data" (program input {depth}) (ok 0)
    verify "depth refusal clears return data" input [] 96 0 store
  let store ← execute "empty init at maximum offset"
    (program input {offset := wordModulus - 1, length := 0}) (ok 0x1234)
  verify "empty init at maximum offset" input [] 0 1 store
  let store ← execute "missing creation callback" (program input {installed := false})
    (.inLeft .word (.word Creation.unavailableReason))
  verify "missing creation callback" input [] 96 0 store
  let store ← execute "creation callback language failure" (program input {fail := true})
    (.inLeft .word (scalar 99))
  verify "creation callback language failure" input [] 96 1 store
  let store ← execute "invalid init range preserves prior return data"
    (program input {offset := wordModulus - 16, length := 32})
    (.inLeft .word (.word Memory.overflowReason))
  verify "invalid init range preserves prior return data" input (bytes [0xaa, 0xbb]) 0 0 store

def run : IO Unit := do
  addressTests
  transportTests
  IO.println "Rust Hull creation tests passed"

end Tests.RustHullCreation
