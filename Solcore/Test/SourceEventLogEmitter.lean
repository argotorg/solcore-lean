import Solcore.Synthesis.Source.EventLogEmitter
import Solcore.Synthesis.Stateful.EventLogExecution

/-! Event-log protocol regressions through actual installed ContractRuntime
code. Golden histories are hand-computed: they cover guarded sites, every frame
part, wrapping arithmetic, empty data, rollback of tentative logs and writes,
and the decoder's rejection of malformed journals. -/
set_option autoImplicit false

namespace Tests.SourceEventLogEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (helpers : List Wire.Expr) (sites : List Site) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "log step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofParts? step sites |
    throw (IO.userError "log wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.EventLog.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"log source emission failed: {reprStr error}")

private def transactions (rows : List (Nat × Nat)) : List EventLogExecution.Transaction :=
  rows.zipIdx.map fun ((flags, input), index) =>
    ⟨"tx-" ++ toString index, Word.ofNatModulo flags, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

private def logRow (topics data : List Nat) : Json := Json.mkObj [
  ("address", toJson "2"), ("topics", toJson (topics.map toString)),
  ("data", toJson ("0x" ++ String.join (data.map hexWord)))]

private def slotRows (slot0 slot1 : Nat) : Json := toJson [
  Json.mkObj [("slot", toJson "0"), ("value", toJson (toString slot0))],
  Json.mkObj [("slot", toJson "1"), ("value", toJson (toString slot1))]]

/-- One hand-computed row: status, payload, slots zero and one, and logs. -/
private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat))
    (expected : List (String × Nat × (Nat × Nat) × List Json)) : IO Unit := do
  let history := EventLogExecution.observe plan (transactions rows) StorageExecution.fixtureBindings 10000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length)
    "log golden history did not complete"
  for (row, (status, payload, (slot0, slot1), logs)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some ("0x" ++ hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slot0 slot1) &&
      (row.getObjVal? "logs").toOption == some (toJson logs))
      s!"log golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x: the result is input + slot 0 and each site value is result + guard.
  let identity ← checked [.var 0] [⟨1, 2, 1⟩, ⟨3, 0, 2⟩]
  historyCheck identity [(2, 5), (9, 1), (8, 0)] [
    ("returned", 5, (5, 1), [logRow [7, 8] [6]]),
    ("reverted", 6, (5, 1), []),
    ("returned", 5, (5, 2), [logRow [] [8, 5]])]
  -- step(x) = x + 1 wraps at the maximum; LOG4 without data; a revert keeps
  -- the committed slots and commits none of its guarded logs.
  let incremented ← checked [increment] [⟨2, 4, 0⟩]
  historyCheck incremented [(4, maximum), (5, 3), (2 ^ 255 + 6, 2)] [
    ("returned", 0, (0, 1), [logRow [4, 5, 6, 7] []]),
    ("reverted", 4, (0, 1), []),
    ("returned", 3, (3, 2), [logRow [7, 8, 9, 10] []])]
  -- No site: flags select only the completion.
  historyCheck (← checked [.var 0] []) [(14, 7), (15, 1)] [
    ("returned", 7, (7, 1), []), ("reverted", 8, (7, 1), [])]

/-- The reverted call's working journal holds every frame record in order; the
public runtime commits the empty checkpoint journal and the prior world. -/
private def tentativeChecks : IO Unit := do
  let plan ← checked [.var 0] [⟨1, 1, 1⟩, ⟨2, 0, 0⟩]
  let bindings := StorageExecution.fixtureBindings
  let world := StorageExecution.initialWorldForContract plan.contract bindings
  let registry : CheckedContractRegistry :=
    ⟨fun address => if address == bindings.address then some plan.contract else none⟩
  let some ⟨contract, installed⟩ := registry.resolve? world bindings.address |
    throw (IO.userError "log contract did not resolve")
  let invocation : TopLevelInvocation := {
    target := bindings.address, caller := bindings.caller, callValue := Word.zero,
    inputData := EventLogExecution.inputData (Word.ofNatModulo 7) (Word.ofNatModulo 3) }
  match TopLevelExecution.run contract invocation installed 0 with
  | .outOfFuel _ _ _ _ _ _ => pure ()
  | .completed _ => throw (IO.userError "zero fuel completed a log call")
  match TopLevelExecution.run contract invocation installed 10000 with
  | .outOfFuel _ _ _ _ _ _ => throw (IO.userError "log golden call exhausted fuel")
  | .completed result =>
      ensure (result.outcome == .reverted (encodeWordBytesBE (Word.ofNatModulo 3)))
        "odd flags did not revert with the result"
      let records := result.workingJournal.logList.map fun entry => (entry.emitter.val, entry.topic.val, entry.payload.val)
      ensure (records == [(2, 256 + 16 + 1, 0), (2, 513, 4), (2, 769, 5), (2, 256, 0)])
        s!"working journal lost the frame order: {reprStr records}"
      ensure (result.committedJournal.logList.isEmpty) "reverted logs were committed"
      let some committed := result.finalWorld.account? bindings.address |
        throw (IO.userError "committed account missing")
      ensure ((committed.storageValue? Word.zero).isNone && (committed.storageValue? (Word.ofNatModulo 1)).isNone)
        "reverted writes were committed"

private def record (topic payload : Nat) (emitter : Nat := 2) : CheckedCoreWordLog :=
  ⟨⟨emitter % addressModulus, Nat.mod_lt _ (by decide)⟩, Word.ofNatModulo topic, Word.ofNatModulo payload⟩

private def decodes (records : List CheckedCoreWordLog) : Option (List (List Nat × List Nat)) :=
  match EventLogExecution.decodeJournal records with
  | .ok events => some (events.map fun event => (event.topics.map (·.val), event.data.map (·.val)))
  | .error _ => none

private def framingChecks : IO Unit := do
  ensure (decodes [] == some []) "empty journal did not decode to no logs"
  ensure (decodes [record 256 0] == some [([], [])]) "LOG0 without data did not decode"
  ensure (decodes [record (256 + 32 + 4) 0, record 513 9, record 514 8, record 769 1, record 770 2,
      record 771 3, record 772 4, record (256 + 1) 0, record 769 5] ==
      some [([1, 2, 3, 4], [9, 8]), ([5], [])]) "complete frames did not decode in order"
  for (records, reason) in [
      ([record 255 0], "a record below the header range"),
      ([record 256 1], "a nonzero header payload"),
      ([record (256 + 5) 0, record 769 1, record 770 1, record 771 1, record 772 1, record 773 1], "five topics"),
      ([record (256 + 48) 0, record 513 1, record 514 1, record 515 1], "three data Words"),
      ([record (256 + 2) 0, record 769 1], "a truncated frame"),
      ([record (256 + 2) 0, record 770 1, record 769 1], "topics out of order"),
      ([record (256 + 16) 0, record 769 1], "a topic in place of data"),
      ([record (256 + 1) 0, record 769 1 3], "mixed emitters"),
      ([record 256 0, record 513 1], "a record after the frames")] do
    ensure (decodes records).isNone s!"decoder accepted {reason}"

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment] [⟨1, 4, 2⟩, ⟨2, 0, 0⟩, ⟨3, 3, 1⟩], ← checked [.var 0] []] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "log plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (Wire.programNodes plan.program == Wire.programNodes plan.step.program + EventLog.programOverhead plan.sites)
      "log wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE saved _ =>
        ensure (Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "log wrapper ignored its arbitrary entry closure"
    | _ => throw (IO.userError "log wrapper lost its initial closure binding")
    ensure ((← emitted plan) == (← emitted plan)) "log emission is nondeterministic"
  let some step := Aggregates.CheckedDAG.ofParts? [.var 0] entry | throw (IO.userError "identity step rejected")
  for sites in [[⟨0, 1, 1⟩], [⟨4, 1, 1⟩], [⟨1, 5, 0⟩], [⟨1, 0, 3⟩], [⟨2, 0, 0⟩, ⟨1, 0, 0⟩],
      [⟨2, 0, 0⟩, ⟨2, 1, 0⟩], [⟨1, 0, 0⟩, ⟨2, 0, 0⟩, ⟨3, 0, 0⟩, ⟨3, 1, 0⟩]] do
    ensure (CheckedPlan.ofParts? step sites).isNone s!"invalid log sites admitted: {reprStr sites}"
  ensure (EventLog.programOverhead [⟨1, 4, 2⟩] > EventLog.programOverhead [⟨1, 3, 2⟩] &&
    EventLog.programOverhead [⟨1, 3, 2⟩] > EventLog.programOverhead [⟨1, 3, 1⟩] &&
    EventLog.programOverhead [⟨1, 3, 1⟩] > EventLog.programOverhead [])
    "log-site simplification does not shrink the program"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {sload, sstore, mload, mstore, revert_, log0 as sc_log0, log2 as sc_log2} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedLogs {",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_old: word = sload(0);", "        let sc_count: word = sload(1);",
  "        let sc_result: word = sc_step(sc_input + sc_old);",
  "        sstore(0, sc_result);", "        sstore(1, sc_count + 1);",
  "        let sc_ptr: word = mload(64);", "        mstore(64, sc_ptr + 64);",
  "        if ((sc_flags & 2) == 2) {",
  "            let sc_value1: word = sc_step(sc_result + 1);",
  "            sc_log0(sc_ptr, 0);", "        }",
  "        if ((sc_flags & 8) == 8) {",
  "            let sc_value3: word = sc_step(sc_result + 3);",
  "            mstore(sc_ptr, sc_value3);", "            mstore(sc_ptr + 32, sc_result);",
  "            sc_log2(sc_ptr, 64, sc_value3 + 1, sc_value3 + 2);", "        }",
  "        if ((sc_flags & 1) == 1) {", "            mstore(sc_ptr, sc_result);",
  "            revert_(sc_ptr, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment] [⟨1, 0, 0⟩, ⟨3, 2, 2⟩])
  ensure (source.source == expectedBasic) "log protocol source changed"
  ensure (source.contractName == "SynthesizedLogs" && source.methodSignature == "run(uint256,uint256)" &&
    source.deployPath == ["SynthesizedLogsDeploy"] && source.runtimePath == ["SynthesizedLogsDeploy", "SynthesizedLogs"])
    "log wrapper metadata changed"
  let none ← emitted (← checked [increment] [])
  ensure ((none.source.splitOn "import {sload, sstore, mload, mstore, revert_} from std.opcodes;").length == 2 &&
    (none.source.splitOn "sc_log").length == 1) "a plan without sites imported or called a log wrapper"
  let one ← emitted (← checked [increment] [⟨2, 4, 1⟩])
  ensure ((one.source.splitOn "revert_, log4 as sc_log4} from std.opcodes;").length == 2 &&
    (one.source.splitOn "            sc_log4(sc_ptr, 32, sc_value2 + 1, sc_value2 + 2, sc_value2 + 3, sc_value2 + 4);").length == 2)
    "LOG4 import or call changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)] [⟨1, 1, 0⟩])
  ensure ((divided.source.splitOn "import {sload, sstore, mload, mstore, revert_, log1 as sc_log1, div as sc_div, ").length == 2)
    "log emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.EventLog.emitterVersion == "solcore-source-event-log-v1" &&
    Solcore.Synthesis.Source.EventLog.wrapperVersion == "solcore-word-event-log-contract-v1" &&
    Solcore.Synthesis.Source.EventLog.selector == "0x7357f5d2" &&
    EventLog.version == "core-event-log-contract-v1" && EventLog.framingVersion == "core-word-log-framing-v1")
    "log provenance changed"

private def observerChecks : IO Unit := do
  ensure (EventLogExecution.calldata (Word.ofNatModulo 2) Word.maximum ==
    "0x7357f5d2" ++ String.ofList (List.replicate 63 '0') ++ "2" ++ String.ofList (List.replicate 64 'f'))
    "log calldata is not selector, flags and input Words"
  let plan ← checked [.var 0] [⟨1, 1, 1⟩]
  let calls := transactions [(2, 2), (3, 1), (0, 0)]
  let exhausted := EventLogExecution.observe plan calls StorageExecution.fixtureBindings 0
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] &&
    rows.length == 1 && (rows[0]!.getObjVal? "logs").toOption == some Json.null &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "log observer conflated fuel exhaustion with completion or claimed unknown logs"
  let complete := EventLogExecution.observe plan calls StorageExecution.fixtureBindings 10000
  ensure ((complete.getObjVal? "observedSlots").toOption == some (toJson (["0", "1"] : List String)) &&
    (complete.getObjVal? "initialLogs").toOption == some (toJson ([] : List Json)) &&
    (complete.getObjValAs? String "framing").toOption == some "core-word-log-framing-v1")
    "history did not declare its slots, deployment logs or framing"

def testSourceEventLogEmitter : IO Unit := do
  admissionChecks
  goldenChecks
  tentativeChecks
  framingChecks
  formattingChecks
  observerChecks

end Tests.SourceEventLogEmitter
