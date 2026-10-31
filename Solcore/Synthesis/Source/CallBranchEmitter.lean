import Solcore.Synthesis.Core.CallBranch
import Solcore.Synthesis.Source.CallSequenceEmitter

/-! Emit the call-branch protocol as two sources with one contract each, under
the call-return profile's wrapper names and methods. The child is the
call-sequence profile's child.

The parent `SynthesizedReturnCaller` has one method `run(uint256 target,
uint256 input)`. It writes `slot 0 + input` to slot 0; in inline Yul it copies
zero bytes at offset 0 into a zeroed scratch Word and reads it back, and takes
`mix = input >> 32`. For each site it reads `returndatasize()` in inline Yul,
then a branch calls when its control bit is set, and a loop calls while its
counter is below its limit and, read in inline Yul, `returndatasize()` differs
from its stop length. Each call goes through std's `raw_call` with the payload
`0x9507d39a ‖ x`, keeps the flag plus twice the copy's length and the copy's
first Word, then reads `returndatasize()` and the call window with a guarded
`returndatacopy`; after the site it reads `returndatasize()` and the exit
window. It writes every slot at the end, sums them and reverts with the sum
under bit 30 of the input. No emitter proof covers these wrappers. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.CallBranch

open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site Kind)
open Solcore.Synthesis.Core.CallSequence (Window)
open Solcore.Synthesis.Source.CallReturn (EmittedContracts)

def emitterVersion : String := "solcore-source-call-branches-v1"
def wrapperVersion : String := "solcore-call-branches-contracts-v1"

private def literal (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

private def stdImports : List String := ["import * from std;", "import * from std.dispatch;"]

private def indent (depth : Nat) (lines : List String) : List String :=
  lines.map fun line => String.ofList (List.replicate (4 * depth) ' ') ++ line

/-- One call: the argument from `mix` and the class byte the expression names,
the call through std's `raw_call`, and the flag plus twice the size and the
first Word into `k` and `f`. -/
private def callLines (classExpr k f : String) : List String :=
  ["let sc_class: word = 0;",
    "assembly {",
    "    sc_class := " ++ classExpr,
    "}",
    "let sc_x: word = ((sc_mix * 256) + sc_class);",
    "let sc_payload: word = allocate_memory(68);",
    "mstore(sc_payload, 36);",
    "mstore((sc_payload + 32), " ++
      literal (Solcore.Synthesis.Core.CallBranch.getSelector * 2 ^ 224) ++ ");",
    "mstore((sc_payload + 36), sc_x);",
    "let sc_data: memory<bytes> = Typedef.abs(sc_payload);",
    "match (raw_call(address(sc_target), uint256(0), sc_data)) {",
    "    case (ok, ret) {",
    "        let sc_ret: word = Typedef.rep(ret);",
    "        let sc_size: word = mload(sc_ret);",
    "        " ++ k ++ " = (frombool(ok) + (2 * sc_size));",
    "        if (sc_size > 31) {",
    "            " ++ f ++ " = mload((sc_ret + 32));",
    "        }",
    "    }",
    "}",
    "sc_calls = (sc_calls + 1);"]

/-- `returndatasize()` into `n` and the window into `v`, in inline Yul. -/
private def readLines (n v : String) (spot : Window) : List String :=
  ["assembly {",
    "    " ++ n ++ " := returndatasize()",
    "    mstore(sc_scratch, 0)",
    "    if iszero(gt(add(" ++ toString spot.offset ++ ", " ++ toString spot.width ++ "), returndatasize())) {",
    "        returndatacopy(sc_scratch, " ++ toString spot.offset ++ ", " ++ toString spot.width ++ ")",
    "    }",
    "    " ++ v ++ " := mload(sc_scratch)",
    "}"]

private def positionName (base : String) (position : Nat) : String := base ++ toString position
private def siteName (base : String) (index : Nat) : String := base ++ toString index

/-- Site `index` at its first position `first`. -/
private def siteLines (site : Site) (index first : Nat) : List String :=
  let p := siteName "sc_p" index
  let entry := ["assembly {", "    " ++ p ++ " := returndatasize()", "}"]
  let body := match site.kind with
    | .branch =>
        let k := positionName "sc_k" first
        let f := positionName "sc_f" first
        let n := positionName "sc_n" first
        let v := positionName "sc_v" first
        let bit := siteName "sc_bit" index
        ["let " ++ bit ++ ": word = 0;",
          "assembly {",
          "    " ++ bit ++ " := and(shr(" ++ toString (Solcore.Synthesis.Core.CallBranch.controlBit index) ++
            ", sc_input), 1)",
          "}",
          "if (" ++ bit ++ " == 1) {"] ++
        indent 1 (callLines ("and(shr(" ++ toString (8 * first) ++ ", sc_input), 255)") k f ++
          readLines n v site.callWindow ++
          ["sc_mix = (((sc_mix + " ++ f ++ ") + " ++ n ++ ") + " ++ v ++ ");"]) ++
        ["}"]
    | .loop =>
        let limit := siteName "sc_limit" index
        let counter := siteName "sc_counter" index
        let go := siteName "sc_go" index
        let condition := "    " ++ go ++ " := and(gt(" ++ limit ++ ", " ++ counter ++ "), iszero(eq(returndatasize(), " ++
          toString site.stop ++ ")))"
        let assign := (List.range site.bound).flatMap fun offset =>
          let position := first + offset
          ["if (" ++ counter ++ " == " ++ toString offset ++ ") {",
            "    " ++ positionName "sc_k" position ++ " = sc_k;",
            "    " ++ positionName "sc_f" position ++ " = sc_f;",
            "    " ++ positionName "sc_n" position ++ " = sc_n;",
            "    " ++ positionName "sc_v" position ++ " = sc_v;",
            "}"]
        ["let " ++ limit ++ ": word = 0;",
          "assembly {",
          "    " ++ limit ++ " := and(shr(" ++ toString (Solcore.Synthesis.Core.CallBranch.controlBit index) ++
            ", sc_input), 3)",
          "    if gt(" ++ limit ++ ", " ++ toString site.bound ++ ") { " ++ limit ++ " := " ++ toString site.bound ++ " }",
          "}",
          "let " ++ counter ++ ": word = 0;",
          "let " ++ go ++ ": word = 0;",
          "assembly {", condition, "}",
          "while (" ++ go ++ " == 1) {"] ++
        indent 1 (["let sc_k: word = 0;", "let sc_f: word = 0;"] ++
          callLines ("and(shr(mul(8, add(" ++ toString first ++ ", " ++ counter ++ ")), sc_input), 255)") "sc_k" "sc_f" ++
          ["let sc_n: word = 0;", "let sc_v: word = 0;"] ++
          readLines "sc_n" "sc_v" site.callWindow ++ assign ++
          ["sc_mix = (((sc_mix + sc_f) + sc_n) + sc_v);",
            counter ++ " = (" ++ counter ++ " + 1);",
            "assembly {", condition, "}"]) ++
        ["}"]
  let a := siteName "sc_a" index
  let u := siteName "sc_u" index
  entry ++ body ++ readLines a u site.exitWindow ++ ["sc_mix = ((sc_mix + " ++ a ++ ") + " ++ u ++ ");"]

/-- The slot values in slot order: slot 0, `z`, each site's three and each
position's four, and the call count. -/
private def slotTerms (sites : List Site) (positions : Nat) : List String :=
  ["sload(0)", "sc_z"] ++
    ((List.range sites.length).flatMap fun index => ["sc_p", "sc_a", "sc_u"].map (siteName · index)) ++
    ((List.range positions).flatMap fun position => ["sc_k", "sc_f", "sc_n", "sc_v"].map (positionName · position)) ++
    ["sc_calls"]

def emit (plan : CheckedPlan) : Except EmitError EmittedContracts := do
  let childText ← Solcore.Synthesis.Source.CallSequence.childSource plan.step
  let sites := plan.sites
  let positions := plan.positions
  let terms := slotTerms sites positions
  let declared := (terms.drop 1).filter (· != "sc_z") |>.filter (· != "sc_calls")
  let sum := match terms with
    | [] => "0"
    | first :: rest => rest.foldl (fun total term => "(" ++ total ++ " + " ++ term ++ ")") first
  let parent := stdImports ++
    [AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "mload", "revert_"] [], "",
    "contract " ++ Solcore.Synthesis.Source.CallReturn.parentContractName ++ " {",
    "    function run(target: uint256, input: uint256) public returns (uint256) {",
    "        let sc_target: word = Typedef.rep(target);",
    "        let sc_input: word = Typedef.rep(input);",
    "        sstore(0, (sload(0) + sc_input));",
    "        let sc_scratch: word = allocate_memory(32);",
    "        let sc_z: word = 1;",
    "        let sc_mix: word = 0;",
    "        assembly {",
    "            mstore(sc_scratch, 0)",
    "            returndatacopy(sc_scratch, 0, 0)",
    "            sc_z := mload(sc_scratch)",
    "            sc_mix := shr(32, sc_input)",
    "        }",
    "        let sc_calls: word = 0;"] ++
    declared.map (fun name => "        let " ++ name ++ ": word = 0;") ++
    indent 2 ((sites.zipIdx.flatMap fun (site, index) =>
      siteLines site index (Solcore.Synthesis.Core.CallBranch.firstPosition sites index))) ++
    ((terms.drop 1).zipIdx.map fun (term, slot) => "        sstore(" ++ toString (slot + 1) ++ ", " ++ term ++ ");") ++
    ["        let sc_sum: word = " ++ sum ++ ";",
    "        let sc_rev: word = 0;",
    "        assembly {",
    "            sc_rev := and(shr(" ++ toString Solcore.Synthesis.Core.CallBranch.revertBit ++ ", sc_input), 1)",
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
    childSource := childText
  }

end Solcore.Synthesis.Source.CallBranch
