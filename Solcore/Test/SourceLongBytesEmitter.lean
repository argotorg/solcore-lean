import Solcore.Synthesis.Source.LongBytesEmitter
import Solcore.Synthesis.Stateful.LongBytesExecution

/-! Long-bytes protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover payloads that reach the
third chunk by one byte, fill all eight chunks, stop one byte into the fourth
chunk, and are empty, together with wrapping arithmetic, the last byte, the
calldata size and a revert that keeps the prior slots. Calldata vectors come
from Foundry's `cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceLongBytesEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.LongBytes (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def modulus : Nat := 2 ^ 256

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "long-bytes step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "long-bytes wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.LongBytes.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"long-bytes source emission failed: {reprStr error}")

/-- `1, 2, 3, ...` wrapping at 256, as bytes. -/
private def ramp (length : Nat) : List UInt8 := (List.range length).map fun index => (index + 1).toUInt8
private def ones (length : Nat) : List UInt8 := List.replicate length 0xff

/-- A big-endian Word of at most 32 bytes, left-aligned as a zero-padded chunk. -/
private def chunk (bytes : List Nat) : Nat :=
  (bytes ++ List.replicate (32 - bytes.length) 0).foldl (fun total byte => total * 256 + byte) 0

/-- Chunk `k` of the wrapping ramp of `length` bytes, cut at the length. -/
private def rampChunk (length k : Nat) : Nat :=
  chunk (((List.range 32).map (· + 32 * k)).filter (· < length) |>.map fun index => (index + 1) % 256)

private def transactions (rows : List (Nat × List UInt8)) : List DynamicBytesExecution.Transaction :=
  rows.zipIdx.map fun ((flags, payload), index) => ⟨"tx-" ++ toString index, Word.ofNatModulo flags, payload⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: status, payload and slots zero to ten. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List UInt8))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := LongBytesExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 100000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows (List.replicate 11 0)))
    "long-bytes golden history did not complete from empty storage"
  for (row, (status, payload, slots)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord (payload % modulus)) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows (slots.map (· % modulus))))
      s!"long-bytes golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x. Sixty-five ramp bytes reach the third chunk by one byte and
  -- leave chunks three to seven untouched; an empty payload keeps the
  -- accumulator and clears the last byte; 256 bytes of 0xff with odd flags
  -- revert with the tentative sum and keep every slot.
  let c0 := rampChunk 65 0
  let c1 := rampChunk 65 1
  let c2 := rampChunk 65 2
  let total := c0 + c1 + c2
  let afterFirst := [total, c0, c0 + c1, total, 0, 0, 0, 0, 0, 65, 65]
  let afterEmpty := [total, c0, c0 + c1, total, 0, 0, 0, 0, 0, 65, 0]
  historyCheck (← checked [.var 0]) [(0, ramp 65), (0, []), (1, ones 256)] [
    ("returned", total + 65 + 65 + 196, afterFirst),
    ("returned", total + 65 + 0 + 100, afterEmpty),
    ("reverted", total + 8 * (modulus - 1) + 321 + 255 + 356, afterEmpty)]
  -- step(x) = x + 1 over all eight chunks of the wrapping ramp, whose last byte
  -- is zero, then 97 bytes, one into the fourth chunk.
  let full := (List.range 8).map (rampChunk 256)
  let partials := (List.range 8).map fun k => (full.take (k + 1)).foldl (· + ·) 0 + (k + 1)
  let first := partials.getD 7 0
  let short := (List.range 4).map (rampChunk 97)
  let continued := (List.range 4).map fun k => first + (short.take (k + 1)).foldl (· + ·) 0 + (k + 1)
  let second := continued.getD 3 0
  historyCheck (← checked [increment]) [(0, ramp 256), (2, ramp 97)] [
    ("returned", first + 256 + 0 + 356, [first] ++ partials ++ [256, 0]),
    ("returned", second + 353 + 97 + 228, [second] ++ continued ++ (partials.drop 4) ++ [353, 97])]

/-- The reverted call's working world holds every write; the public runtime
commits the prior, here empty, world. -/
private def rollbackChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "long-bytes contract did not resolve")
  let some input := DynamicBytesExecution.inputData? (Word.ofNatModulo 1) (ramp 65) |
    throw (IO.userError "long-bytes calldata exceeded the Word-sized input bound")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  let c0 := rampChunk 65 0
  let c1 := rampChunk 65 1
  let total := c0 + c1 + rampChunk 65 2
  match TopLevelExecution.run contract invocation installed 100000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "long-bytes golden call exhausted fuel")
  | .completed terminal =>
      ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo (total + 65 + 65 + 196))))
        "odd flags did not revert with the tentative sum"
      let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ((List.range 11).map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) ==
          [total, c0, c0 + c1, total, 0, 0, 0, 0, 0, 65, 65])
        "the working world lost a chunk, count or last-byte write"
      let some committed := terminal.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ((List.range 11).all fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone)
        "the reverted writes were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "long-bytes plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (LongBytes.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + LongBytes.programOverhead + LongBytes.guardNodes)
      "long-bytes wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "long-bytes wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "long-bytes wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "long-bytes emission is nondeterministic"
  ensure (LongBytes.programOverhead == 102 && LongBytes.guardNodes == 296 && LongBytes.maxPayloadBytes == 256 &&
    LongBytes.countSlot == 9 && LongBytes.tailSlot == 10) "long-bytes wrapper size or layout changed"

/-- Chunk `k`'s four source lines, written out independently of the emitter. -/
private def expectedChunk (k : Nat) : List String :=
  ["        if (sc_length > " ++ toString (32 * k) ++ ") {",
    "            sc_acc = sc_step(sc_acc + mload(sc_data + " ++ toString (32 * k + 32) ++ "));",
    "            sstore(" ++ toString (k + 1) ++ ", sc_acc);", "        }"]

private def expectedBasic : String := String.intercalate "\n" ([
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_, mload, calldatasize} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedLongBytes {",
  "    function run(flags: uint256, payload: memory<bytes>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_data: word = Typedef.rep(payload);",
  "        let sc_length: word = mload(sc_data);",
  "        let sc_acc: word = sload(0);"] ++
  expectedChunk 0 ++ expectedChunk 1 ++ expectedChunk 2 ++ expectedChunk 3 ++
  expectedChunk 4 ++ expectedChunk 5 ++ expectedChunk 6 ++ expectedChunk 7 ++ [
  "        let sc_tail: word = mload(sc_data + sc_length) & 255;",
  "        sstore(0, sc_acc);",
  "        let sc_total: word = sload(9) + sc_length;",
  "        sstore(9, sc_total);", "        sstore(10, sc_tail);",
  "        let sc_result: word = sload(0) + sload(9) + sload(10) + calldatasize();",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""])

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "long-bytes protocol source changed"
  ensure (source.contractName == "SynthesizedLongBytes" && source.methodSignature == "run(uint256,bytes)" &&
    source.deployPath == ["SynthesizedLongBytesDeploy"] &&
    source.runtimePath == ["SynthesizedLongBytesDeploy", "SynthesizedLongBytes"])
    "long-bytes wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, mload, calldatasize, div as sc_div, ").length == 2)
    "long-bytes emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.LongBytes.emitterVersion == "solcore-source-long-bytes-v1" &&
    Solcore.Synthesis.Source.LongBytes.wrapperVersion == "solcore-word-long-bytes-contract-v1" &&
    Solcore.Synthesis.Source.LongBytes.selector == "0x220eb9b6" && LongBytes.version == "core-long-bytes-contract-v1")
    "long-bytes provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,bytes)" 1 0xabab...ab` (65 bytes) from the pinned Foundry release.
  ensure (DynamicBytesExecution.calldata (Word.ofNatModulo 1) (List.replicate 65 0xab) ==
    "0x220eb9b6" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 62 '0') ++ "40" ++
      String.ofList (List.replicate 62 '0') ++ "41" ++ String.join (List.replicate 65 "ab") ++
      String.ofList (List.replicate 62 '0'))
    "65-byte calldata differs from the canonical zero-padded encoding"
  ensure ([0, 1, 64, 65, 97, 255, 256].map (fun length =>
      (DynamicBytesExecution.inputBytes Word.zero (List.replicate length 7)).size) == [100, 132, 164, 196, 228, 356, 356])
    "long-bytes calldata sizes are not the head, length and padded payload"
  let plan ← checked [.var 0]
  let calls := transactions [(0, ramp 129), (1, ramp 256), (0, [])]
  let exhausted := LongBytesExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "long-bytes observer conflated fuel exhaustion with completion"
  let complete := LongBytesExecution.observe plan calls StorageExecution.fixtureBindings 100000
  ensure ((complete.getObjVal? "observedSlots").toOption ==
      some (toJson ((List.range 11).map toString)) &&
    (complete.getObjValAs? String "schema").toOption == some "solcore-lean.long-bytes-history.v1" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its slots or schema"

def testSourceLongBytesEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  rollbackChecks
  formattingChecks
  observerChecks

end Tests.SourceLongBytesEmitter
