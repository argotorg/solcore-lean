import Solcore.Frontend.RustHull.Precompiles
import Solcore.Core.Machine
import Solcore.Core.Check

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
