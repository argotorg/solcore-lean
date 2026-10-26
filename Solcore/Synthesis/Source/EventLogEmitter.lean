import Solcore.Synthesis.Core.EventLog
import Solcore.Synthesis.Source.AggregateRenderer

/-! Emit the fixed event-log protocol. Slot zero receives the step result and
slot one the counter, in the same order as the original Core contract. Each
guarded site then applies the step to `result + guard` and calls the pinned
`std.opcodes` wrapper `log0` to `log4` with its topics and data Words, over a
64-byte buffer reserved from the free-memory pointer. Odd flags revert after
every write and log with the result encoded as exactly 32 bytes; even flags
return it through the ABI. Only the log arities a plan uses are imported. The
arbitrary checked aggregate entry is preserved. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.EventLog

open Solcore.Synthesis.Core.EventLog (CheckedPlan Site)

def emitterVersion : String := "solcore-source-event-log-v1"
def wrapperVersion : String := "solcore-word-event-log-contract-v1"
def contractName : String := "SynthesizedLogs"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedLogsDeploy"]
def runtimePath : List String := ["SynthesizedLogsDeploy", "SynthesizedLogs"]

/-- The wrapper alias of a topic count; the `sc_` prefix avoids the generic
`log1` that `std` exports. -/
def logAlias (topics : Nat) : String := "sc_log" ++ toString topics

/-- Arities used by the plan, ascending and without duplicates. -/
def usedArities (sites : List Site) : List Nat :=
  (List.range 5).filter fun topics => sites.any (·.topics == topics)

private def siteLines (site : Site) : List String :=
  let value := "sc_value" ++ toString site.guard
  let mask := toString (2 ^ site.guard)
  let data := (List.range site.dataWords).map fun index =>
    "            mstore(sc_ptr" ++ (if index = 0 then "" else " + 32") ++ ", " ++
      (if index = 0 then value else "sc_result") ++ ");"
  let topics := (List.range site.topics).map fun index => value ++ " + " ++ toString (index + 1)
  ["        if ((sc_flags & " ++ mask ++ ") == " ++ mask ++ ") {",
    "            let " ++ value ++ ": word = sc_step(sc_result + " ++ toString site.guard ++ ");"] ++ data ++
    ["            " ++ logAlias site.topics ++ "(" ++ ", ".intercalate
      (["sc_ptr", toString (32 * site.dataWords)] ++ topics) ++ ");", "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let wrappers := (usedArities plan.sites).map fun topics => "log" ++ toString topics ++ " as " ++ logAlias topics
  let mut lines := ["import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith (["sload", "sstore", "mload", "mstore", "revert_"] ++ wrappers)
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
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = sload(0);",
    "        let sc_count: word = sload(1);",
    "        let sc_result: word = sc_step(sc_input + sc_old);",
    "        sstore(0, sc_result);",
    "        sstore(1, sc_count + 1);",
    "        let sc_ptr: word = mload(64);",
    "        mstore(64, sc_ptr + 64);"] ++ plan.sites.flatMap siteLines ++
    ["        if ((sc_flags & 1) == 1) {",
    "            mstore(sc_ptr, sc_result);",
    "            revert_(sc_ptr, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.EventLog
