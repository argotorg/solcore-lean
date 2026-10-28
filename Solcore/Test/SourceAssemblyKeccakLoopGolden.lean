import Solcore.Synthesis.Source.AssemblyKeccakLoopCases
import Solcore.Test.SourceKeccakLoopGolden

/-! Golden cases for the inline Yul Keccak-loop profile. The contract of each
form is written out by hand for the plan with loop mask seven and key mask
one, and the step functions must be the Keccak-loop profile's. The Keccak-loop
profile's hand-written rows, with every entry and log, must come back through
the new cases: every golden plan, in every form, is emitted as an inline Yul
case, decoded, and its unchanged Core reference observed. A changed
expectation must fail. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyKeccakLoopGolden

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Tests.SourceKeccakLoopGolden (Expected goldenPlans)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

private def head : List String := [
  "contract SynthesizedAssemblyKeccakLoops {",
  "    acc: word;",
  "    entries: mapping(word => word);",
  "",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 7);",
  "        let sc_base: word = (sc_input & ~7);",
  "        let sc_counter: word = 0;",
  "        let sc_key: word = 0;"]

private def locals : List String := [
  "        let sc_sum: word = 0;",
  "        let sc_value: word = 0;",
  "        let sc_result: word = 0;",
  "        let sc_ptr: word = 0;",
  "        assembly {",
  "            sc_ptr := mload(64)",
  "            mstore(64, add(sc_ptr, 64))",
  "        }"]

private def tail : List String := [
  "        assembly {",
  "            sc_result := add(sload(0), sc_limit)",
  "            if and(sc_flags, 1) {",
  "                mstore(sc_ptr, sc_result)",
  "                revert(sc_ptr, 32)",
  "            }",
  "        }",
  "        return uint256(sc_result);",
  "    }",
  "}"]

/-- The contract of the plan with loop mask seven and key mask one in each form. -/
private def contracts : List (Form × List String) := [
  (.split, head ++ locals ++ [
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_sum := add(add(sload(keccak256(sc_ptr, 64)), sload(0)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sstore(keccak256(sc_ptr, 64), sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "            }",
    "            sc_counter = (sc_counter + 1);",
    "        }"] ++ tail),
  (.carried, head ++ ["        let sc_slot: word = 0;"] ++ locals ++ [
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_slot := keccak256(sc_ptr, 64)",
    "                sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "                sc_counter := add(sc_counter, 1)",
    "            }",
    "        }"] ++ tail),
  (.pipelined, head ++ ["        let sc_slot: word = 0;"] ++ locals ++ [
    "        assembly {",
    "            if gt(sc_limit, sc_counter) {",
    "                sc_key := or(sc_base, and(sc_counter, 1))",
    "                mstore(sc_ptr, 1)",
    "                mstore(add(sc_ptr, 32), sc_key)",
    "                sc_slot := keccak256(sc_ptr, 64)",
    "                sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "            }",
    "        }",
    "        while (sc_limit > sc_counter) {",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                mstore(sc_ptr, sc_value)",
    "                log2(sc_ptr, 32, sc_counter, sc_key)",
    "                sc_counter := add(sc_counter, 1)",
    "                if gt(sc_limit, sc_counter) {",
    "                    sc_key := or(sc_base, and(sc_counter, 1))",
    "                    mstore(sc_ptr, 1)",
    "                    mstore(add(sc_ptr, 32), sc_key)",
    "                    sc_slot := keccak256(sc_ptr, 64)",
    "                    sc_sum := add(add(sload(sc_slot), sload(0)), sc_input)",
    "                }",
    "            }",
    "        }"] ++ tail)]

/-- The source before the contract, without its `std.opcodes` import. -/
private def stepPart (source : String) : List String :=
  ((source.splitOn "contract ").headD "").splitOn "\n" |>.filter (!·.endsWith "from std.opcodes;")

/-- Every row of a golden plan through the inline Yul case of one form. -/
private def checkRows (name : String) (form : Form) (mask keyMask constant : Nat)
    (rows : List (KeccakLoopExecution.Transaction × Expected)) (fuel : Nat) : IO Unit := do
  let step ← Tests.SourceKeccakLoopGolden.step constant
  let some plan := KeccakLoop.CheckedPlan.ofParts? step mask keyMask
    | throw (IO.userError s!"{name}: the Keccak-loop wrapper failed admission")
  let transactions := rows.map Prod.fst
  let loop ← get (Solcore.Synthesis.Source.KeccakLoop.checkedScenario plan transactions)
  let json ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.emitCase ⟨loop, form⟩
    (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((Solcore.Synthesis.Source.AssemblyKeccakLoop.replayCase json fuel).toOption == some json)
    s!"{name} {form.name}: the case does not replay"
  let scenario ← get (Solcore.Synthesis.Source.AssemblyKeccakLoop.caseProgram json)
  ensure (scenario.form == form) s!"{name} {form.name}: the decoded form differs"
  let slots := scenario.loop.observedSlots
  let history := Solcore.Synthesis.Source.AssemblyKeccakLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name} {form.name}: the history is incomplete"
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := KeccakLoopExecution.model step fuel mask keyMask transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name} {form.name}: a row is missing"
  for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
    Tests.SourceKeccakLoopGolden.check s!"{name} {form.name} {transaction.id}" slots row model expected

def testSourceAssemblyKeccakLoopGolden : IO Unit := do
  let fuel := 1000000
  -- Each form's contract, and the Keccak-loop profile's step functions.
  let step ← Tests.SourceKeccakLoopGolden.step 2
  let some plan := KeccakLoop.CheckedPlan.ofParts? step 7 1
    | throw (IO.userError "the plan with masks seven and one failed admission")
  let parent ← get ((Solcore.Synthesis.Source.KeccakLoop.emit plan).mapError reprStr)
  for (form, expected) in contracts do
    let emitted ← get ((Solcore.Synthesis.Source.AssemblyKeccakLoop.emit form plan).mapError reprStr)
    let some contract := (emitted.source.splitOn "contract ").getLast?
      | throw (IO.userError "the emitted source has no contract")
    ensure (("contract " ++ contract) == String.intercalate "\n" expected ++ "\n")
      s!"{form.name}: the emitted contract differs from the golden text:\n{contract}"
    ensure (stepPart emitted.source == stepPart parent.source && !occurs emitted.source "revert_(" &&
        !occurs emitted.source "sc_log2" && !occurs emitted.source "entries[" &&
        !occurs emitted.source "from std.opcodes")
      s!"{form.name}: the step functions or imports differ from the Keccak-loop profile's"
  -- The Keccak-loop profile's rows, through every form.
  for (name, mask, keyMask, constant, rows, _) in goldenPlans do
    for form in Form.all do
      checkRows name form mask keyMask constant rows fuel
  -- A changed expectation fails.
  let some (name, mask, keyMask, constant, rows, _) := goldenPlans.head? | throw (IO.userError "no golden plan")
  let some ((transaction, expected), rest) := rows.getLast?.map (fun last => (last, rows.dropLast))
    | throw (IO.userError "no golden row")
  let changed := rest ++ [(transaction, {expected with output := expected.output + 1})]
  let failed ← tryCatch (do checkRows name .pipelined mask keyMask constant changed fuel; pure false)
    (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAssemblyKeccakLoopGolden
