import Solcore.Synthesis.Core.CallSequence
import Solcore.Synthesis.Source.CallReturnEmitter

/-! Emit the call-sequence protocol as two sources with one contract each,
under the call-return profile's wrapper names and methods. The child
`SynthesizedReturnCallee` has one method `get(uint256 x)`: it follows the
original Core child in order, the step over `x` and slot 0 and the writes of
slots 0 and 1, then computes the length from the class byte in inline Yul,
writes `d0`, `d1` and `d2` to memory and ends with `revert_` for an odd class
byte, otherwise with `return_`.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0; in inline Yul it copies
zero bytes at offset 0 into a zeroed scratch Word and reads it back, and takes
`mix = input >> 32`. For each call it reads `returndatasize()` in inline Yul,
calls the target with std's `raw_call` and the payload `0x9507d39a ‖ x`, keeps
the flag, the copy's length and its first Word when it has one, then reads
`returndatasize()` and copies the plan's window with `returndatacopy` in
inline Yul when it lies inside the data; from the second call on it re-reads
call 1's copy's first Word. It writes every slot at the end, sums them with
slot 0 and reverts with the sum under bit 24 of the input. No emitter proof
covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallSequence

open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)
open Solcore.Synthesis.Source.CallReturn (EmittedContracts)

def emitterVersion : String := "solcore-source-call-sequences-v1"
def wrapperVersion : String := "solcore-call-sequences-contracts-v1"

/-- A Word as a hexadecimal literal. -/
private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def multiplierLiteral : String := literal Solcore.Synthesis.Core.CallSequence.multiplier

private def stdImports : List String := ["import * from std;", "import * from std.dispatch;"]

private def name (prefix_ : String) (call : Nat) : String := prefix_ ++ toString call

/-- Call `call`, from one: the argument, the read before the call, the call,
the reads after it and, from the second call on, the re-read of call 1's copy. -/
private def callLines (call : Nat) (spot : Window) : List String :=
  let n := fun base => name base call
  ["        let " ++ n "sc_class" ++ ": word = 0;",
    "        assembly {",
    "            " ++ n "sc_class" ++ " := and(shr(" ++ toString (8 * (call - 1)) ++ ", sc_input), 255)",
    "        }",
    "        let " ++ n "sc_x" ++ ": word = ((sc_mix * 256) + " ++ n "sc_class" ++ ");",
    "        let " ++ n "sc_payload" ++ ": word = allocate_memory(68);",
    "        mstore(" ++ n "sc_payload" ++ ", 36);",
    "        mstore((" ++ n "sc_payload" ++ " + 32), " ++
      literal (Solcore.Synthesis.Core.CallSequence.getSelector * 2 ^ 224) ++ ");",
    "        mstore((" ++ n "sc_payload" ++ " + 36), " ++ n "sc_x" ++ ");",
    "        let " ++ n "sc_data" ++ ": memory<bytes> = Typedef.abs(" ++ n "sc_payload" ++ ");",
    "        let " ++ n "sc_p" ++ ": word = 1;",
    "        assembly {",
    "            " ++ n "sc_p" ++ " := returndatasize()",
    "        }",
    "        let " ++ n "sc_ok" ++ ": word = 0;"] ++
  (if call > 1 then ["        let " ++ n "sc_size" ++ ": word = 0;", "        let " ++ n "sc_ret" ++ ": word = 0;"] else []) ++
  ["        let " ++ n "sc_first" ++ ": word = 0;",
    "        match (raw_call(address(sc_target), uint256(0), " ++ n "sc_data" ++ ")) {",
    "            case (ok, ret) {",
    "                " ++ n "sc_ok" ++ " = frombool(ok);",
    "                " ++ n "sc_ret" ++ " = Typedef.rep(ret);",
    "                " ++ n "sc_size" ++ " = mload(" ++ n "sc_ret" ++ ");",
    "                if (" ++ n "sc_size" ++ " > 31) {",
    "                    " ++ n "sc_first" ++ " = mload((" ++ n "sc_ret" ++ " + 32));",
    "                }",
    "            }",
    "        }",
    "        let " ++ n "sc_n" ++ ": word = 0;",
    "        let " ++ n "sc_c" ++ ": word = 0;",
    "        assembly {",
    "            " ++ n "sc_n" ++ " := returndatasize()",
    "            mstore(sc_scratch, 0)",
    "            if iszero(gt(add(" ++ toString spot.offset ++ ", " ++ toString spot.width ++ "), returndatasize())) {",
    "                returndatacopy(sc_scratch, " ++ toString spot.offset ++ ", " ++ toString spot.width ++ ")",
    "            }",
    "            " ++ n "sc_c" ++ " := mload(sc_scratch)",
    "        }"] ++
  (if call > 1 then
    ["        if (sc_size1 > 31) {",
      "            sc_again = (sc_again + mload((sc_ret1 + 32)));",
      "        }"]
  else []) ++
  ["        sc_mix = (((sc_mix + " ++ n "sc_first" ++ ") + " ++ n "sc_n" ++ ") + " ++ n "sc_c" ++ ");"]

/-- Call `call`'s five slot writes. -/
private def storeLines (call : Nat) : List String :=
  let n := fun base => name base call
  let slot := fun offset => toString (5 * call - 3 + offset)
  ["        sstore(" ++ slot 0 ++ ", (" ++ n "sc_ok" ++ " + (2 * " ++ n "sc_size" ++ ")));",
    "        sstore(" ++ slot 1 ++ ", " ++ n "sc_first" ++ ");",
    "        sstore(" ++ slot 2 ++ ", " ++ n "sc_p" ++ ");",
    "        sstore(" ++ slot 3 ++ ", " ++ n "sc_n" ++ ");",
    "        sstore(" ++ slot 4 ++ ", " ++ n "sc_c" ++ ");"]

/-- The terms of the sum, in the order the slots hold them. -/
private def sumTerms (calls : Nat) : List String :=
  ["sload(0)", "sc_z0"] ++ (List.range calls).flatMap (fun index =>
    let n := fun base => name base (index + 1)
    [n "sc_ok", "(2 * " ++ n "sc_size" ++ ")", n "sc_first", n "sc_p", n "sc_n", n "sc_c"]) ++ ["sc_again"]

private def sumExpression (calls : Nat) : String :=
  match sumTerms calls with
  | [] => "0"
  | first :: rest => rest.foldl (fun total term => "(" ++ total ++ " + " ++ term ++ ")") first

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let mut names : List String := []
  let mut child := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "return_", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let helper := "sc_fn" ++ toString index
    child := child ++ ["function " ++ helper ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := helper :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  child := child ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.childContractName ++ " {",
    "    function get(x: uint256) public returns (uint256) {",
    "        let sc_x: word = Typedef.rep(x);",
    "        let sc_o: word = sload(0);",
    "        let sc_c: word = (sload(1) + 1);",
    "        let sc_r: word = sc_step((sc_x + sc_o));",
    "        sstore(0, sc_r);",
    "        sstore(1, sc_c);",
    "        let sc_len: word = 0;",
    "        assembly {",
    "            sc_len := and(shr(1, sc_x), 127)",
    "            if gt(sc_len, " ++ toString Solcore.Synthesis.Core.CallSequence.capacity ++ ") { sc_len := " ++
      toString Solcore.Synthesis.Core.CallSequence.capacity ++ " }",
    "        }",
    "        let sc_d0: word = (sc_r * " ++ multiplierLiteral ++ ");",
    "        let sc_d1: word = ((sc_c * " ++ multiplierLiteral ++ ") ^ sc_x);",
    "        let sc_d2: word = (sc_d0 ^ sc_d1);",
    "        let sc_p: word = allocate_memory(96);",
    "        mstore(sc_p, sc_d0);",
    "        mstore((sc_p + 32), sc_d1);",
    "        mstore((sc_p + 64), sc_d2);",
    "        if ((sc_x & 1) == 1) {",
    "            revert_(sc_p, sc_len);",
    "        }",
    "        return_(sc_p, sc_len);",
    "        return uint256(0);",
    "    }",
    "}"]
  let calls := plan.calls
  let parent := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_scratch: word = allocate_memory(32);",
    "        let sc_z0: word = 1;",
    "        let sc_mix: word = 0;",
    "        assembly {",
    "            mstore(sc_scratch, 0)",
    "            returndatacopy(sc_scratch, 0, 0)",
    "            sc_z0 := mload(sc_scratch)",
    "            sc_mix := shr(32, sc_input)",
    "        }",
    "        let sc_again: word = 0;",
    "        let sc_ret1: word = 0;",
    "        let sc_size1: word = 0;"] ++
    (plan.windows.zipIdx.flatMap fun (spot, index) => callLines (index + 1) spot) ++
    ["        sstore(1, sc_z0);"] ++
    ((List.range calls).flatMap fun index => storeLines (index + 1)) ++
    ["        sstore(" ++ toString (5 * calls + 2) ++ ", sc_again);",
    "        let sc_sum: word = " ++ sumExpression calls ++ ";",
    "        let sc_rev: word = 0;",
    "        assembly {",
    "            sc_rev := and(shr(24, sc_input), 1)",
    "        }",
    "        if (sc_rev == 1) {",
    "            mstore(0, sc_sum);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_sum);",
    "    }",
    "}"]
  return {
    parentSource := String.intercalate "\n" parent ++ "\n"
    childSource := String.intercalate "\n" child ++ "\n"
  }

end Solcore.Synthesis.Source.CallSequence
