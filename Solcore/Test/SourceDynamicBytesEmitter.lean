import Solcore.Synthesis.Source.DynamicBytesEmitter
import Solcore.Synthesis.Stateful.DynamicBytesExecution

/-! Bytes protocol regressions through actual installed ContractRuntime code.
Golden histories are hand-computed: they cover empty payloads, lengths on both
sides of the Word boundary, a payload filling both chunks, zero padding of a
partial chunk, wrapping arithmetic, the last byte, the calldata size and a
revert that keeps the prior slots. Calldata vectors come from Foundry's
`cast calldata` encoder. -/
set_option autoImplicit false

namespace Tests.SourceDynamicBytesEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "bytes step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "bytes wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.DynamicBytes.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"bytes source emission failed: {reprStr error}")

private def ramp (length : Nat) : List UInt8 := (List.range length).map fun index => (index + 1).toUInt8
private def ones (length : Nat) : List UInt8 := List.replicate length 0xff

/-- A big-endian Word of at most 32 bytes, left-aligned as a zero-padded chunk. -/
private def chunk (bytes : List Nat) : Nat :=
  (bytes ++ List.replicate (32 - bytes.length) 0).foldl (fun total byte => total * 256 + byte) 0

private def transactions (rows : List (Nat × List UInt8)) : List DynamicBytesExecution.Transaction :=
  rows.zipIdx.map fun ((flags, payload), index) => ⟨"tx-" ++ toString index, Word.ofNatModulo flags, payload⟩

private def slotRows (values : List Nat) : Json := toJson (values.zipIdx.map fun (value, slot) =>
  Json.mkObj [("slot", toJson (toString slot)), ("value", toJson (toString value))])

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- One hand-computed row: status, payload and slots zero to four. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × List UInt8))
    (expected : List (String × Nat × List Nat)) : IO Unit := do
  let history := DynamicBytesExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows [0, 0, 0, 0, 0]))
    "bytes golden history did not complete from empty storage"
  for (row, (status, payload, slots)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slots))
      s!"bytes golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x. An empty payload returns only the 100-byte calldata size; one
  -- byte 0x80 is the chunk 2^255; a reverted 33-byte payload keeps the slots.
  let high := 2 ^ 255
  let first := chunk ((List.range 32).map (· + 1))
  historyCheck (← checked [.var 0]) [(0, []), (0, [0x80]), (1, ramp 33)] [
    ("returned", 100, [0, 0, 0, 0, 0]),
    ("returned", high + 1 + 128 + 132, [high, high, 0, 1, 128]),
    ("reverted", high + first + chunk [33] + 34 + 33 + 164, [high, high, 0, 1, 128])]
  -- step(x) = x + 1 wraps at the maximum. Forty-eight ramp bytes fill one
  -- chunk and half of the other, whose zero padding contributes nothing.
  let lower := chunk ((List.range 32).map (· + 1))
  let upper := chunk ((List.range 16).map (· + 33))
  let folded := lower + upper + 2
  historyCheck (← checked [increment]) [(0, ones 32), (2, ramp 48), (3, [1])] [
    ("returned", 32 + 255 + 132, [0, 0, 0, 32, 255]),
    ("returned", folded + 80 + 48 + 164, [folded, lower + 1, folded, 80, 48]),
    ("reverted", folded + chunk [1] + 1 + 81 + 1 + 132, [folded, lower + 1, folded, 80, 48])]
  -- A partial chunk of 0xff bytes is masked to the payload length.
  let partialOnes := chunk (List.replicate 17 255)
  historyCheck (← checked [.var 0]) [(0, ones 17), (0, ones 64)] [
    ("returned", partialOnes + 17 + 255 + 132, [partialOnes, partialOnes, 0, 17, 255]),
    ("returned", (partialOnes + 2 * maximum + 81 + 255 + 164) % 2 ^ 256,
      [(partialOnes + 2 * maximum) % 2 ^ 256, (partialOnes + maximum) % 2 ^ 256,
        (partialOnes + 2 * maximum) % 2 ^ 256, 81, 255])]

/-- The reverted call's working world holds every write; the public runtime
commits the prior, here empty, world. -/
private def rollbackChecks : IO Unit := do
  let plan ← checked [.var 0]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "bytes contract did not resolve")
  let some input := DynamicBytesExecution.inputData? (Word.ofNatModulo 1) (ramp 33) |
    throw (IO.userError "bytes calldata exceeded the Word-sized input bound")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
  let first := chunk ((List.range 32).map (· + 1))
  let folded := first + chunk [33]
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "bytes golden call exhausted fuel")
  | .completed terminal =>
      ensure (terminal.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo (folded + 33 + 33 + 164))))
        "odd flags did not revert with the tentative sum"
      let some working := terminal.terminalContext.context.values.working.1.account? bindings.address |
        throw (IO.userError "working account missing")
      ensure ([0, 1, 2, 3, 4].map (fun slot => (working.storageRead (Word.ofNatModulo slot)).val) ==
          [folded, first, folded, 33, 33])
        "the working world lost a chunk, count or last-byte write"
      let some committed := terminal.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ([0, 1, 2, 3, 4].all fun slot => (committed.storageValue? (Word.ofNatModulo slot)).isNone)
        "the reverted writes were committed"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "bytes plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (DynamicBytes.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program == Wire.programNodes plan.step.program + DynamicBytes.programOverhead)
      "bytes wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "bytes wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "bytes wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "bytes emission is nondeterministic"
  ensure (DynamicBytes.programOverhead == 176) "bytes wrapper overhead changed"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mstore, revert_, mload, calldatasize} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedBytes {",
  "    function run(flags: uint256, payload: memory<bytes>) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_data: word = Typedef.rep(payload);",
  "        let sc_length: word = mload(sc_data);",
  "        let sc_acc: word = sload(0);",
  "        if (sc_length > 0) {",
  "            sc_acc = sc_step(sc_acc + mload(sc_data + 32));",
  "            sstore(1, sc_acc);", "        }",
  "        if (sc_length > 32) {",
  "            sc_acc = sc_step(sc_acc + mload(sc_data + 64));",
  "            sstore(2, sc_acc);", "        }",
  "        let sc_tail: word = mload(sc_data + sc_length) & 255;",
  "        sstore(0, sc_acc);",
  "        let sc_total: word = sload(3) + sc_length;",
  "        sstore(3, sc_total);", "        sstore(4, sc_tail);",
  "        let sc_result: word = sload(0) + sload(3) + sload(4) + calldatasize();",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "bytes protocol source changed"
  ensure (source.contractName == "SynthesizedBytes" && source.methodSignature == "run(uint256,bytes)" &&
    source.deployPath == ["SynthesizedBytesDeploy"] &&
    source.runtimePath == ["SynthesizedBytesDeploy", "SynthesizedBytes"])
    "bytes wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {sload, sstore, mstore, revert_, mload, calldatasize, div as sc_div, ").length == 2)
    "bytes emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.DynamicBytes.emitterVersion == "solcore-source-dynamic-bytes-v1" &&
    Solcore.Synthesis.Source.DynamicBytes.wrapperVersion == "solcore-word-dynamic-bytes-contract-v1" &&
    Solcore.Synthesis.Source.DynamicBytes.selector == "0x220eb9b6" && DynamicBytes.version == "core-dynamic-bytes-contract-v1")
    "bytes provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,bytes)"` vectors from the pinned Foundry release.
  ensure (DynamicBytesExecution.calldata (Word.ofNatModulo 2) [] ==
    "0x220eb9b6" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 62 '0') ++ "40" ++
      String.ofList (List.replicate 64 '0'))
    "empty bytes calldata differs from the canonical encoding"
  ensure (DynamicBytesExecution.calldata (Word.ofNatModulo 1) (List.replicate 33 0xab) ==
    "0x220eb9b6" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 62 '0') ++ "40" ++
      String.ofList (List.replicate 62 '0') ++ "21" ++ String.join (List.replicate 33 "ab") ++
      String.ofList (List.replicate 62 '0'))
    "33-byte calldata differs from the canonical zero-padded encoding"
  ensure ([0, 1, 31, 32, 33, 64].map (fun length =>
      (DynamicBytesExecution.inputBytes Word.zero (List.replicate length 7)).size) == [100, 132, 132, 132, 164, 164])
    "bytes calldata sizes are not the head, length and padded payload"
  let plan ← checked [.var 0]
  let calls := transactions [(0, ramp 17), (1, ramp 33), (0, [])]
  let exhausted := DynamicBytesExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "bytes observer conflated fuel exhaustion with completion"
  let complete := DynamicBytesExecution.observe plan calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1", "2", "3", "4"] : List String)) &&
    (complete.getObjValAs? String "schema").toOption == some "solcore-lean.bytes-history.v1" &&
    (complete.getObjValAs? String "status").toOption == some "complete")
    "history did not declare its slots or schema"

def testSourceDynamicBytesEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  rollbackChecks
  formattingChecks
  observerChecks

end Tests.SourceDynamicBytesEmitter
