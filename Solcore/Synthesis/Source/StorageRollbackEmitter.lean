import Solcore.Synthesis.Core.StorageRollback
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed two-slot rollback protocol. Odd original inputs revert after
both writes, returning the tentative reread sum as exactly 32 bytes. Even inputs
return that same Word through the ABI. Memory at zero is touched only immediately
before the terminal revert. The arbitrary checked aggregate entry is preserved.
`ScalarMeaning.StorageRollback.emit_source_meaning` relates the emitted text to
the original Core contract's top-level transaction, returned or reverted, under
an independent rollback source semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageRollback

open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-rollback-v2"
def wrapperVersion : String := "solcore-word-storage-rollback-contract-v1"
def contractName : String := "SynthesizedRollback"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRollbackDeploy"]
def runtimePath : List String := ["SynthesizedRollbackDeploy", "SynthesizedRollback"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old0: word = sload(0);",
    "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);",
    "        sstore(1, sc_old1 + 1);",
    "        let sc_final0: word = sload(0);",
    "        let sc_final1: word = sload(1);",
    "        let sc_result: word = sc_final0 + sc_final1;",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageRollback
