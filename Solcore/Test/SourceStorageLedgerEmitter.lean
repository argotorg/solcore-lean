import Solcore.Synthesis.Source.StorageLedgerEmitter
import Solcore.Synthesis.Stateful.StorageLedgerExecution

/-! Sender-keyed ledger protocol regressions through actual installed
ContractRuntime code. Every sender and recipient slot is checked against
Foundry's `cast keccak`. Golden histories are hand-computed: they cover two
senders, a sender spending what it received, an insufficient balance that
reverts with the credited balance, an odd-flags revert after a sufficient
transfer, a self-transfer and a wrapping payload. -/
set_option autoImplicit false

namespace Tests.SourceStorageLedgerEmitter

open Lean Solcore.Core Solcore.ContractRuntime Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)
open Solcore.Synthesis.Source (EmittedProgram)
open Solcore.Synthesis.Stateful

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def entry : Wire.Expr := .apply (.var 1) (.var 0)
private def increment : Wire.Expr := .binary .wordAdd (.var 0) (word 1)
private def maximum : Nat := 2 ^ 256 - 1

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Anvil's first three default accounts, as decimal addresses. -/
private def s0 : Nat := 1390849295786071768276380950238675083608645509734
private def s1 : Nat := 642829559307850963015472508762062935916233390536
private def s2 : Nat := 344073830386746567427978432078835137280280269756

/-- `cast keccak` of the base slot one followed by each key, as decimal Words. -/
private def castSlots : List (Nat × Nat) := [
  (s0, 78570585682356430730071959328554860354235701529430903318287531160901974441362),
  (s1, 20716297545289759526027067151373890095476849666992757577977631027685962156767),
  (s2, 41239936133192089133110966148978916085433226010267689210672645629181891175976),
  (0, 78541660797044910968829902406342334108369226379826116161446442989268089806461),
  (2 ^ 160 - 1, 43383778025841973631710988075798902187352068724127397131308783529513977091473),
  (maximum, 71124947674796991739310909576881207026731009306364129481614628957978744178186)]

private def castSlot (key : Nat) : Nat := ((castSlots.find? (·.1 == key)).map (·.2)).getD 0

private def sender (address : Nat) : IO Address := do
  let some value := StorageLedgerExecution.senders.find? (·.val == address) |
    throw (IO.userError s!"{address} is not a fixed sender")
  return value

private def checked (helpers : List Wire.Expr) : IO CheckedPlan := do
  let some step := Aggregates.CheckedDAG.ofParts? helpers entry |
    throw (IO.userError "ledger step did not pass the checked aggregate profile")
  let some plan := CheckedPlan.ofStep? step |
    throw (IO.userError "ledger wrapper did not pass the full Wire host checker")
  return plan

private def emitted (plan : CheckedPlan) : IO EmittedProgram :=
  match Solcore.Synthesis.Source.StorageLedger.emit plan with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"ledger source emission failed: {reprStr error}")

private def slotChecks : IO Unit := do
  ensure ((StorageLedgerExecution.senders.map (·.val)) == [s0, s1, s2]) "the fixed senders changed"
  for (key, expected) in castSlots do
    ensure ((StorageMappingExecution.entrySlot (Word.ofNatModulo key)).val == expected)
      s!"entry slot of key {key} differs from cast keccak"
  for address in [s0, s1, s2] do
    ensure ((StorageLedgerExecution.senderSlot (← sender address)).val == castSlot address)
      s!"sender slot of {address} differs from cast keccak"
  ensure (StorageLedger.hashNodes == 2654 && StorageLedger.programOverhead == 115)
    "the Keccak closure or the ledger wrapper changed size"

private def transactions (rows : List (Nat × Nat × Nat × Nat × Nat)) : IO (List StorageLedgerExecution.Transaction) :=
  rows.zipIdx.mapM fun ((from_, flags, recipient, amount, input), index) => do
    return ⟨"tx-" ++ toString index, ← sender from_, Word.ofNatModulo flags, Word.ofNatModulo recipient,
      Word.ofNatModulo amount, Word.ofNatModulo input⟩

/-- Sixty-four lowercase hexadecimal digits, written without the observer's
byte encoder. -/
private def hexWord (value : Nat) : String :=
  let digits := Nat.toDigits 16 value
  "0x" ++ String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

/-- The declared slots in increasing order with the values the golden assigns. -/
private def slotRows (slots : List Nat) (values : List (Nat × Nat)) : Json :=
  toJson ((slots.mergeSort (· ≤ ·)).map fun slot => Json.mkObj [("slot", toJson (toString slot)),
    ("value", toJson (toString (((values.find? (·.1 == slot)).map (·.2)).getD 0)))])

private def historyCheck (plan : CheckedPlan) (rows : List (Nat × Nat × Nat × Nat × Nat)) (slots : List Nat)
    (expected : List (String × Nat × List (Nat × Nat))) : IO Unit := do
  let history := StorageLedgerExecution.observe plan (← transactions rows) StorageExecution.fixtureBindings 1000000
  let observed := (history.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((history.getObjValAs? String "status").toOption == some "complete" && observed.length == expected.length &&
    (history.getObjVal? "observedSlots").toOption == some (toJson ((slots.mergeSort (· ≤ ·)).map toString)) &&
    (history.getObjVal? "initialStorage").toOption == some (slotRows slots []))
    "ledger golden history did not complete from empty declared slots"
  for (row, (status, payload, values)) in observed.zip expected do
    ensure ((row.getObjValAs? String "status").toOption == some status &&
      (row.getObjValAs? String "output").toOption == some (hexWord payload) &&
      (row.getObjVal? "committedStorage").toOption == some (slotRows slots values))
      s!"ledger golden row changed: {row.compress}"

private def goldenChecks : IO Unit := do
  -- step(x) = x + 1. The first sender credits 8 and pays 1 to the second; a
  -- transfer of 2^64 from the credited 8 reverts with 8; the second sender
  -- spends what it received and its odd flags revert the sufficient transfer.
  let slots := [0, castSlot s0, castSlot s1, castSlot s2]
  historyCheck (← checked [increment]) [(s0, 0, s1, 1, 7), (s0, 0, s1, 2 ^ 64, 0), (s1, 1, s2, 1, 0)] slots [
    ("returned", 9, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("reverted", 8, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("reverted", 4, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)])]
  -- The same transfer with even flags commits.
  historyCheck (← checked [increment]) [(s0, 0, s1, 1, 7), (s1, 0, s2, 1, 0)] [0, castSlot s0, castSlot s1, castSlot s2] [
    ("returned", 9, [(0, 1), (castSlot s0, 7), (castSlot s1, 1)]),
    ("returned", 4, [(0, 2), (castSlot s0, 7), (castSlot s1, 1), (castSlot s2, 1)])]
  -- step(x) = x. A self-transfer of the whole credit leaves it; crediting the
  -- maximum and paying 2^70 to the largest key wraps the returned sum to one.
  historyCheck (← checked [.var 0]) [(s2, 0, s2, 7, 7), (s1, 0, maximum, 2 ^ 70, maximum)]
    [0, castSlot s2, castSlot s1, castSlot maximum] [
    ("returned", 15, [(0, 1), (castSlot s2, 7)]),
    ("returned", 1, [(0, 2), (castSlot s2, 7), (castSlot s1, maximum - 2 ^ 70), (castSlot maximum, 2 ^ 70)])]

private def admissionChecks : IO Unit := do
  for plan in [← checked [increment], ← checked [.var 0]] do
    ensure (plan.program.check && plan.program.toCore.checkHost &&
      plan.program.resultType == .sum .word (.sum .word .word) && plan.contract.entryProfile == .wordOutcomeV1)
      "ledger plan lost full host checking or the typed outcome convention"
    ensure (plan.contract.code.program == plan.program.toCore) "admission replaced the original contract"
    ensure (StorageLedger.canonicalNodes plan.step == Wire.programNodes plan.program &&
      Wire.programNodes plan.program ==
        Wire.programNodes plan.step.program + StorageLedger.programOverhead + StorageLedger.hashNodes)
      "ledger wrapper overhead differs from the complete original Core"
    match plan.program.body with
    | .letE hash (.letE saved _) =>
        ensure (Wire.encodeExpr hash == Wire.encodeExpr StorageMapping.hashClosure &&
          Wire.encodeExpr saved == Wire.encodeExpr plan.step.program.body)
          "ledger wrapper lost its hash closure or ignored its arbitrary entry closure"
    | _ => throw (IO.userError "ledger wrapper lost its initial closure bindings")
    ensure ((← emitted plan) == (← emitted plan)) "ledger emission is nondeterministic"

private def expectedBasic : String := String.intercalate "\n" [
  "import * from std;", "import * from std.dispatch;",
  "import {caller, mstore, revert_} from std.opcodes;", "",
  "function sc_fn0(sc_arg: word) returns (word) {",
  "    let sc_v0: word = 1;", "    let sc_v1: word = (sc_arg + sc_v0);",
  "    return sc_v1;", "}", "",
  "function sc_step(sc_arg: word) returns (word) {",
  "    let sc_v0: word = sc_fn0(sc_arg);", "    return sc_v0;", "}", "",
  "contract SynthesizedLedger {",
  "    counter: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, recipient: uint256, amount: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_recipient: word = Typedef.rep(recipient);",
  "        let sc_amount: word = Typedef.rep(amount);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_sender: word = caller();",
  "        let sc_balance: word = entries[sc_sender] + sc_step(sc_input);",
  "        if (sc_amount > sc_balance) {", "            mstore(0, sc_balance);",
  "            revert_(0, 32);", "        }",
  "        entries[sc_sender] = sc_balance - sc_amount;",
  "        entries[sc_recipient] = entries[sc_recipient] + sc_amount;",
  "        counter = counter + 1;",
  "        let sc_result: word = entries[sc_sender] + entries[sc_recipient] + counter;",
  "        if ((sc_flags & 1) == 1) {", "            mstore(0, sc_result);",
  "            revert_(0, 32);", "        }",
  "        return uint256(sc_result);", "    }", "}", ""]

private def formattingChecks : IO Unit := do
  let source ← emitted (← checked [increment])
  ensure (source.source == expectedBasic) "ledger protocol source changed"
  ensure (source.contractName == "SynthesizedLedger" &&
    source.methodSignature == "run(uint256,uint256,uint256,uint256)" &&
    source.deployPath == ["SynthesizedLedgerDeploy"] &&
    source.runtimePath == ["SynthesizedLedgerDeploy", "SynthesizedLedger"])
    "ledger wrapper metadata changed"
  -- Raw primitives join the same opcode import only when a step uses them.
  let divided ← emitted (← checked [.binary .wordDiv (.var 0) (word 1)])
  ensure ((divided.source.splitOn "import {caller, mstore, revert_, div as sc_div, ").length == 2)
    "ledger emission lost the merged raw division alias"
  ensure (Solcore.Synthesis.Source.StorageLedger.emitterVersion == "solcore-source-sender-ledger-v1" &&
    Solcore.Synthesis.Source.StorageLedger.wrapperVersion == "solcore-word-sender-ledger-contract-v1" &&
    Solcore.Synthesis.Source.StorageLedger.selector == "0x15509d2b" &&
    StorageLedger.version == "core-sender-ledger-contract-v1") "ledger provenance changed"

private def observerChecks : IO Unit := do
  -- `cast calldata "run(uint256,uint256,uint256,uint256)" 1 <second sender> 7 9`
  ensure (StorageLedgerExecution.calldata (Word.ofNatModulo 1) (Word.ofNatModulo s1) (Word.ofNatModulo 7)
      (Word.ofNatModulo 9) ==
    "0x15509d2b" ++ String.ofList (List.replicate 63 '0') ++ "1" ++ String.ofList (List.replicate 24 '0') ++
      "70997970c51812dc3a010c7d01b50e0d17dc79c8" ++ String.ofList (List.replicate 63 '0') ++ "7" ++
      String.ofList (List.replicate 63 '0') ++ "9")
    "ledger calldata is not the selector and four Words"
  let calls ← transactions [(s0, 0, s1, 1, 7), (s1, 0, 0, 1, 3), (s0, 1, s0, 0, 0)]
  let declared := (StorageLedgerExecution.observedSlots calls).map (·.val)
  ensure (declared == [0, castSlot s0, castSlot s1, castSlot 0].mergeSort (· ≤ ·))
    "declared slots are not the counter and every sender's and recipient's entry slot in order"
  let plan ← checked [.var 0]
  -- The deployer in the bindings never acts; each transaction's sender does.
  let first := StorageLedgerExecution.observe plan calls StorageExecution.fixtureBindings 1000000
  let other := StorageLedgerExecution.observe plan calls ⟨⟨33, by decide⟩, ⟨202, by decide⟩⟩ 1000000
  ensure ((first.getObjVal? "transactions").toOption == (other.getObjVal? "transactions").toOption &&
    (first.getObjValAs? String "status").toOption == some "complete")
    "ledger rows depended on the deployer instead of the senders"
  let moved ← transactions [(s2, 0, s1, 1, 7), (s1, 0, 0, 1, 3), (s0, 1, s0, 0, 0)]
  let swapped := StorageLedgerExecution.observe plan moved StorageExecution.fixtureBindings 1000000
  ensure ((swapped.getObjVal? "observedSlots").toOption != (first.getObjVal? "observedSlots").toOption)
    "a different sender kept the same declared slots"
  let exhausted := StorageLedgerExecution.observe plan calls StorageExecution.fixtureBindings 1000
  let rows := (exhausted.getObjValAs? (List Json) "transactions").toOption.getD []
  ensure ((exhausted.getObjValAs? String "status").toOption == some "incomplete" &&
    (exhausted.getObjValAs? (List String) "unexecuted").toOption == some ["tx-1", "tx-2"] && rows.length == 1 &&
    (rows[0]!.getObjValAs? String "status").toOption == some "out-of-fuel" &&
    (exhausted.getObjVal? "finalStorage").toOption == (exhausted.getObjVal? "initialStorage").toOption)
    "ledger observer conflated fuel exhaustion with completion"
  ensure ((first.getObjValAs? String "schema").toOption == some "solcore-lean.ledger-history.v1")
    "history did not declare its schema"

def testSourceStorageLedgerEmitter : IO Unit := do
  slotChecks
  admissionChecks
  goldenChecks
  formattingChecks
  observerChecks

end Tests.SourceStorageLedgerEmitter
