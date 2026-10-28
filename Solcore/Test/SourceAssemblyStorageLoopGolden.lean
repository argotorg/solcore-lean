import Solcore.Synthesis.Source.AssemblyStorageLoopCases
import Solcore.Test.SourceStorageLoopGolden

/-! Golden cases for the inline Yul storage-loop profile. The contract of each
form is written out by hand for the mask-three plan, and the step functions
must be the storage-loop profile's. The storage-loop profile's hand-written
rows must come back through the new cases: every golden plan, in every form,
is emitted as an inline Yul case, decoded, and its unchanged Core reference
observed. A changed expectation must fail. -/
set_option autoImplicit false

namespace Tests.SourceAssemblyStorageLoopGolden

open Lean
open Solcore.Synthesis.Core
open Solcore.Synthesis.Stateful
open Solcore.Synthesis.Source.AssemblyStorage (Form)
open Tests.SourceStorageLoopGolden (Expected goldenPlans)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def head : List String := [
  "contract SynthesizedAssemblyStorageLoops {",
  "    function run(flags: uint256, input: uint256) public returns (uint256) {",
  "        let sc_flags: word = Typedef.rep(flags);",
  "        let sc_input: word = Typedef.rep(input);",
  "        let sc_limit: word = (sc_input & 3);",
  "        let sc_counter: word = 0;"]

private def tail : List String := [
  "        assembly {",
  "            sstore(1, add(sload(1), sc_limit))",
  "            sc_result := add(sload(0), sload(1))",
  "            if and(sc_flags, 1) {",
  "                mstore(0, sc_result)",
  "                revert(0, 32)",
  "            }",
  "        }",
  "        return uint256(sc_result);",
  "    }",
  "}"]

/-- The contract of the mask-three plan in each form. -/
private def contracts : List (Form × List String) := [
  (.split, head ++ [
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                let sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(add(sc_counter, 2), sc_value)",
    "                sstore(0, sc_value)",
    "            }",
    "            sc_counter = (sc_counter + 1);",
    "        }"] ++ tail),
  (.carried, head ++ [
    "        let sc_slot: word = 0;",
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            assembly {",
    "                sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                sc_counter := add(sc_counter, 1)",
    "            }",
    "        }"] ++ tail),
  (.pipelined, head ++ [
    "        let sc_slot: word = 0;",
    "        let sc_sum: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_result: word = 0;",
    "        assembly {",
    "            if gt(sc_limit, sc_counter) {",
    "                sc_slot := add(sc_counter, 2)",
    "                sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "            }",
    "        }",
    "        while (sc_limit > sc_counter) {",
    "            sc_value = sc_step(sc_sum);",
    "            assembly {",
    "                sstore(sc_slot, sc_value)",
    "                sstore(0, sc_value)",
    "                sc_counter := add(sc_counter, 1)",
    "                if gt(sc_limit, sc_counter) {",
    "                    sc_slot := add(sc_counter, 2)",
    "                    sc_sum := add(add(add(add(sload(0), sload(1)), sload(sub(sc_slot, 1))), sload(sc_slot)), sc_input)",
    "                }",
    "            }",
    "        }"] ++ tail)]

private def occurs (text part : String) : Bool := (text.splitOn part).length > 1

/-- The source before the contract, without its `std.opcodes` import. -/
private def stepPart (source : String) : List String :=
  ((source.splitOn "contract ").headD "").splitOn "\n" |>.filter (!·.endsWith "from std.opcodes;")

/-- Every row of a golden plan through the inline Yul case of one form. -/
private def checkRows (name : String) (form : Form) (mask constant : Nat)
    (rows : List (StorageLoopExecution.Transaction × Expected)) (fuel : Nat) : IO Unit := do
  let step ← Tests.SourceStorageLoopGolden.step constant
  let some plan := StorageLoop.CheckedPlan.ofParts? step mask
    | throw (IO.userError s!"{name}: the storage-loop wrapper failed admission")
  let transactions := rows.map Prod.fst
  let loop ← get (Solcore.Synthesis.Source.StorageLoop.checkedScenario plan transactions)
  let json ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.emitCase ⟨loop, form⟩
    (Json.mkObj [("kind", toJson "imported")]) fuel)
  ensure ((Solcore.Synthesis.Source.AssemblyStorageLoop.replayCase json fuel).toOption == some json)
    s!"{name} {form.name}: the case does not replay"
  let scenario ← get (Solcore.Synthesis.Source.AssemblyStorageLoop.caseProgram json)
  ensure (scenario.form == form) s!"{name} {form.name}: the decoded form differs"
  let history := Solcore.Synthesis.Source.AssemblyStorageLoop.observe scenario StorageExecution.fixtureBindings fuel
  ensure ((history.getObjValAs? String "status").toOption == some "complete") s!"{name} {form.name}: the history is incomplete"
  let observed ← get (history.getObjValAs? (Array Json) "transactions")
  let some modelled := StorageLoopExecution.model step fuel mask transactions
    | throw (IO.userError s!"{name}: the source-loop model failed")
  ensure (observed.size == rows.length && modelled.length == rows.length) s!"{name} {form.name}: a row is missing"
  for ((row, model), (transaction, expected)) in (observed.toList.zip modelled).zip rows do
    Tests.SourceStorageLoopGolden.check s!"{name} {form.name} {transaction.id}" row model expected

def testSourceAssemblyStorageLoopGolden : IO Unit := do
  let fuel := 1000000
  -- Each form's contract, and the storage-loop profile's step functions.
  let step ← Tests.SourceStorageLoopGolden.step 2
  let some plan := StorageLoop.CheckedPlan.ofParts? step 3
    | throw (IO.userError "the mask-three plan failed admission")
  let parent ← get ((Solcore.Synthesis.Source.StorageLoop.emit plan).mapError reprStr)
  for (form, expected) in contracts do
    let emitted ← get ((Solcore.Synthesis.Source.AssemblyStorageLoop.emit form plan).mapError reprStr)
    let some contract := (emitted.source.splitOn "contract ").getLast?
      | throw (IO.userError "the emitted source has no contract")
    ensure (("contract " ++ contract) == String.intercalate "\n" expected ++ "\n")
      s!"{form.name}: the emitted contract differs from the golden text:\n{contract}"
    ensure (stepPart emitted.source == stepPart parent.source && !occurs emitted.source "revert_(" &&
        !occurs emitted.source "from std.opcodes")
      s!"{form.name}: the step functions or imports differ from the storage-loop profile's"
  -- The storage-loop profile's rows, through every form.
  for (name, mask, constant, rows) in goldenPlans do
    for form in Form.all do
      checkRows name form mask constant rows fuel
  -- A changed expectation fails.
  let some (name, mask, constant, rows) := goldenPlans.head? | throw (IO.userError "no golden plan")
  let some ((transaction, expected), rest) := rows.getLast?.map (fun last => (last, rows.dropLast))
    | throw (IO.userError "no golden row")
  let changed := rest ++ [(transaction, {expected with output := expected.output + 1})]
  let failed ← tryCatch (do checkRows name .pipelined mask constant changed fuel; pure false)
    (fun _ => pure true)
  ensure failed "a changed expectation passed"

end Tests.SourceAssemblyStorageLoopGolden
