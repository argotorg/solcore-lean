import Solcore.Synthesis.Core.StorageLedger
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed sender-keyed ledger protocol. The contract declares the
mapping profile's `counter` field at slot zero and `entries: mapping(word =>
word)` field at base slot one, reads the sender with `caller()` from
`std.opcodes` and never computes a slot itself: indexing goes through the
pinned std, which hashes the base slot followed by the key. The credit, the
insufficient-balance revert, the two entry writes, the counter update, the
rereads and the odd-flags revert follow the original Core contract in order.
Memory at zero is touched only before a terminal revert, after the std's own
hashing scratch use. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLedger

open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)

def emitterVersion : String := "solcore-source-sender-ledger-v1"
def wrapperVersion : String := "solcore-word-sender-ledger-contract-v1"
def contractName : String := "SynthesizedLedger"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedLedgerDeploy"]
def runtimePath : List String := ["SynthesizedLedgerDeploy", "SynthesizedLedger"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["caller", "mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    counter: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++
      "(flags: uint256, recipient: uint256, amount: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_recipient: word = Typedef.rep(recipient);",
    "        let sc_amount: word = Typedef.rep(amount);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_sender: word = caller();",
    "        let sc_balance: word = entries[sc_sender] + sc_step(sc_input);",
    "        if (sc_amount > sc_balance) {",
    "            mstore(0, sc_balance);",
    "            revert_(0, 32);",
    "        }",
    "        entries[sc_sender] = sc_balance - sc_amount;",
    "        entries[sc_recipient] = entries[sc_recipient] + sc_amount;",
    "        counter = counter + 1;",
    "        let sc_result: word = entries[sc_sender] + entries[sc_recipient] + counter;",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageLedger
