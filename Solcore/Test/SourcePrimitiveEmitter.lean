import Solcore.Synthesis.Source.PrimitiveEmitter
import Solcore.Synthesis.Source.InputEmitter
import Solcore.Core.Machine
import Solcore.Core.Wire.Codec.Program

/-! Primitive printer regressions and independently executed Core boundaries.
These checks do not claim to execute Rust, EVM or emitted source. -/
set_option autoImplicit false

namespace Tests.SourcePrimitiveEmitter

open Solcore.Core
open Solcore.Synthesis.Core
open Solcore.Synthesis.Source

private def word (value : Nat) : Wire.Expr := .word (Word.ofNatModulo value)
private def high : Nat := 2 ^ 255
private def maximum : Nat := Word.maximum.val

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checked (body : Wire.Expr) : IO CheckedWordFunction :=
  match CheckedWordFunction.ofBody? body with
  | some function => pure function
  | none => throw (IO.userError "primitive fixture failed its Core or profile check")

private def emitted (function : CheckedWordFunction) : IO EmittedProgram :=
  match Primitive.emit function with
  | .ok program => pure program
  | .error error => throw (IO.userError s!"primitive emission failed: {reprStr error}")

private def observe (body : Wire.Expr) (input expected : Nat) : IO Unit := do
  let function ← checked body
  let program := function.instantiate (Word.ofNatModulo input)
  ensure program.check "primitive application failed Core typing"
  match program.toCore.runStateful 2000 with
  | .done (.word actual) _ =>
      ensure (actual.val == expected) s!"primitive Core result differs: got {actual.val}, expected {expected}"
  | _ => throw (IO.userError "primitive Core application did not complete")

/-- The newly supported operations, including a signed predicate used at runtime. -/
def fixtures : List (String × Wire.Expr) := [
  ("div", .binary .wordDiv (.var 0) (word 2)),
  ("mod", .binary .wordMod (.var 0) (word 2)),
  ("shl", .binary .wordShl (.var 0) (word 1)),
  ("shr", .binary .wordShr (.var 0) (word 1)),
  ("sar", .binary .wordSar (.var 0) (word 1)),
  ("sdiv", .binary .wordSdiv (.var 0) (word maximum)),
  ("smod", .binary .wordSmod (.var 0) (word 2)),
  ("sgt", .ifE (.binary .wordSgt (.var 0) (word 0)) (word 1) (word 0)),
  ("addmod", .ternary .wordAddMod (.var 0) (word 1) (word maximum)),
  ("mulmod", .ternary .wordMulMod (.var 0) (word 2) (word maximum)),
  ("clz", .unary .wordClz (.var 0)),
  ("byte", .binary .wordByte (word 31) (.var 0)),
  ("pow", .binary .wordPow (.var 0) (word 2)),
  ("signextend", .binary .wordSignExtend (word 0) (.var 0))]

private def ordinaryChecks : IO Unit := do
  for (label, body) in fixtures do
    let function ← checked body
    ensure (PrimitiveRenderer.supported function.body) s!"supported primitive excluded: {label}"
    let source ← emitted function
    ensure (source == (← emitted function)) s!"primitive emission is not deterministic: {label}"
    ensure (source.contractName == "SynthesizedPrimitives" && source.methodName == "run" &&
      source.methodSignature == "run(uint256)" && source.deployPath == ["SynthesizedPrimitivesDeploy"] &&
      source.runtimePath == ["SynthesizedPrimitivesDeploy", "SynthesizedPrimitives"])
      "primitive wrapper metadata changed"
    let some restored := CheckedWordFunction.ofProgram? function.program |
      throw (IO.userError "primitive original failed readmission")
    ensure (Wire.encodeProgram restored.program == Wire.encodeProgram function.program)
      "primitive emission changed the original Core program"
  for (label, input, expected) in [
      ("div", 0, 0), ("div", 1, 0), ("div", maximum, high - 1), ("div", high, high / 2),
      ("mod", 0, 0), ("mod", 1, 1), ("mod", maximum, 1), ("mod", high, 0),
      ("shl", 1, 2), ("shl", maximum, maximum - 1), ("shl", high, 0),
      ("shr", 1, 0), ("shr", maximum, high - 1), ("shr", high, high / 2),
      ("sar", 5, 2), ("sar", maximum, maximum), ("sar", high, high + high / 2),
      ("sdiv", 7, maximum - 6), ("sdiv", maximum, 1), ("sdiv", high, high),
      ("smod", 7, 1), ("smod", maximum - 6, maximum), ("smod", high, 0),
      ("sgt", 0, 0), ("sgt", 1, 1), ("sgt", maximum, 0), ("sgt", high, 0), ("sgt", high - 1, 1),
      ("addmod", 0, 1), ("addmod", maximum, 1), ("addmod", maximum - 1, 0),
      ("mulmod", 0, 0), ("mulmod", maximum, 0), ("mulmod", high, 1),
      ("clz", 0, 256), ("clz", 1, 255), ("clz", 2, 254),
      ("clz", maximum, 0), ("clz", high, 0), ("clz", high - 1, 1),
      ("byte", 1, 1), ("byte", maximum, 255), ("byte", high, 0),
      ("pow", 0, 0), ("pow", 1, 1), ("pow", maximum, 1), ("pow", high, 0),
      ("signextend", 127, 127), ("signextend", 128, maximum - 127),
      ("signextend", 255, maximum), ("signextend", 256, 0), ("signextend", high, 0)] do
    let some (_, body) := fixtures.find? (fun item => item.1 == label) |
      throw (IO.userError s!"missing primitive fixture {label}")
    observe body input expected

private def boundaryChecks : IO Unit := do
  for operation in [Wire.BinaryOp.wordDiv, .wordMod, .wordSdiv, .wordSmod] do
    for input in [0, 1, maximum, high] do
      observe (.binary operation (.var 0) (word 0)) input 0
  for operation in [Wire.TernaryOp.wordAddMod, .wordMulMod] do
    for input in [0, 1, maximum, high] do
      observe (.ternary operation (.var 0) (word maximum) (word 0)) input 0
      observe (.ternary operation (.var 0) (word maximum) (word 1)) input 0
  for (amount, expected) in [(0, 1), (1, 2), (255, high), (256, 0), (257, 0), (maximum, 0)] do
    observe (.binary .wordShl (word 1) (.var 0)) amount expected
  for (amount, expected) in [(0, maximum), (1, high - 1), (255, 1), (256, 0), (maximum, 0)] do
    observe (.binary .wordShr (word maximum) (.var 0)) amount expected
  for amount in [255, 256, 257, maximum] do
    observe (.binary .wordSar (word high) (.var 0)) amount maximum
    observe (.binary .wordSar (word (high - 1)) (.var 0)) amount 0
  observe (.binary .wordSdiv (.var 0) (word 2)) (maximum - 6) (maximum - 2)
  observe (.binary .wordSdiv (.var 0) (word (maximum - 1))) (maximum - 6) 3
  observe (.binary .wordSmod (.var 0) (word (maximum - 1))) (maximum - 6) maximum
  observe (.binary .wordSmod (.var 0) (word (maximum - 1))) 7 1
  observe (.binary .wordSmod (.var 0) (word maximum)) high 0
  observe (.ifE (.binary .wordSgt (.var 0) (word high)) (word 1) (word 0)) maximum 1
  observe (.ternary .wordAddMod (.var 0) (word maximum) (word (maximum - 1))) maximum 2
  observe (.ternary .wordMulMod (.var 0) (word maximum) (word (maximum - 1))) maximum 1

private def byteExponentChecks : IO Unit := do
  for (index, expected) in [(0, 128), (1, 0), (30, 18), (31, 52), (32, 0), (256, 0), (maximum, 0)] do
    observe (.binary .wordByte (.var 0) (word (high + 4660))) index expected
  for (index, expected) in [(0, maximum - 127), (1, 128), (31, 128), (32, 128), (maximum, 128)] do
    observe (.binary .wordSignExtend (.var 0) (word 128)) index expected
  observe (.binary .wordSignExtend (word 0) (.var 0)) 384 (maximum - 127)
  observe (.binary .wordSignExtend (word 1) (.var 0)) 32768 (maximum - 32767)
  for index in [31, 32, 256, maximum] do
    observe (.binary .wordSignExtend (word index) (.var 0)) high high
  for input in [0, 1, maximum, high] do
    observe (.binary .wordPow (.var 0) (word 0)) input 1
  for (base, exponent, expected) in [
      (0, 1, 0), (0, high, 0), (1, maximum, 1),
      (2, 255, high), (2, 256, 0), (2, high, 0), (2, maximum, 0),
      (maximum, maximum, maximum), (maximum, high, 1), (high, 1, high)] do
    observe (.binary .wordPow (word base) (.var 0)) exponent expected

private def legacyScalarChecks : IO Unit := do
  for (body, expected) in [
      (.unary .wordNot (.var 0), maximum - 5),
      (.ifE (.unary .boolNot (.binary .wordEq (.var 0) (word 0))) (word 1) (word 0), 1),
      (.binary .wordAdd (.var 0) (word maximum), 4),
      (.binary .wordSub (.var 0) (word 6), maximum),
      (.binary .wordMul (.var 0) (word 3), 15),
      (.binary .wordAnd (.var 0) (word 3), 1),
      (.binary .wordOr (.var 0) (word 3), 7),
      (.binary .wordXor (.var 0) (word 3), 6),
      (.ifE (.binary .wordEq (.var 0) (word 5)) (word 1) (word 0), 1),
      (.ifE (.binary .wordGt (.var 0) (word 4)) (word 1) (word 0), 1)] do
    ensure (PrimitiveRenderer.supported body) "primitive profile excluded an existing scalar operation"
    let _ ← emitted (← checked body)
    observe body 5 expected

private def renderLines (target : Target) (body : Wire.Expr) : IO (List String) :=
  match PrimitiveRenderer.render target ["sc_input"] 8 0 body with
  | .ok value => pure value.lines
  | .error error => throw (IO.userError s!"primitive formatting fixture rejected: {reprStr error}")

private def formattingChecks : IO Unit := do
  let shift : Wire.Expr := .binary .wordShl
    (.letE (word 7) (.binary .wordAdd (.var 0) (.var 1)))
    (.letE (word 1) (.var 0))
  ensure ((← renderLines .word shift) == [
    "        let sc_v0: word = 7;", "        let sc_v1: word = sc_v0;",
    "        let sc_v2: word = (sc_v1 + sc_input);", "        let sc_v3: word = sc_v2;",
    "        let sc_v4: word = 1;", "        let sc_v5: word = sc_v4;",
    "        let sc_v6: word = sc_v5;", "        let sc_v7: word = sc_shl(sc_v6, sc_v3);"])
    "shift emission changed operand order, scope or captured argument order"
  observe shift 2 18
  ensure ((← renderLines .word (.ternary .wordAddMod (.var 0) (word 1) (word 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = 1;",
    "        let sc_v2: word = sc_v1;", "        let sc_v3: word = 0;",
    "        let sc_v4: word = sc_v3;", "        let sc_v5: word = sc_addmod(sc_v0, sc_v2, sc_v4);"])
    "modular emission did not evaluate all three original arguments in order"
  ensure ((← renderLines .bool (.binary .wordSgt (.var 0) (word 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = 0;",
    "        let sc_v2: word = sc_v1;", "        let sc_v3: bool = tobool(sc_sgt(sc_v0, sc_v2));"])
    "signed predicate did not convert the raw Word result to Bool"
  ensure ((← renderLines .word (.unary .wordClz (.var 0))) == [
    "        let sc_v0: word = sc_input;", "        let sc_v1: word = sc_clz(sc_v0);"])
    "count-leading-zero emission did not preserve its operand"
  for (operation, alias) in [(Wire.BinaryOp.wordByte, "sc_byte"), (.wordSignExtend, "sc_signextend"),
      (.wordPow, "sc_exp")] do
    ensure ((← renderLines .word (.binary operation (.var 0) (word 3))) == [
      "        let sc_v0: word = sc_input;", "        let sc_v1: word = 3;",
      "        let sc_v2: word = sc_v1;", "        let sc_v3: word = " ++ alias ++ "(sc_v0, sc_v2);"])
      "index/value or base/exponent operands were reordered"
  let branch : Wire.Expr := .ifE (.bool true)
    (.letE (word 3) (.binary .wordDiv (.var 1) (.var 0)))
    (.letE (word 0) (.binary .wordMod (.var 1) (.var 0)))
  ensure ((← renderLines .word branch) == [
    "        let sc_v0: bool = true;", "        let sc_v1: word = 0;", "        if (sc_v0) {",
    "            let sc_v2: word = 3;", "            let sc_v3: word = sc_v2;",
    "            let sc_v4: word = sc_input;", "            let sc_v5: word = sc_v3;",
    "            let sc_v6: word = sc_div(sc_v4, sc_v5);", "            sc_v1 = sc_v6;", "        } else {",
    "            let sc_v7: word = 0;", "            let sc_v8: word = sc_v7;",
    "            let sc_v9: word = sc_input;", "            let sc_v10: word = sc_v8;",
    "            let sc_v11: word = sc_mod(sc_v9, sc_v10);", "            sc_v1 = sc_v11;", "        }"])
    "raw operation or local escaped its conditional branch"
  observe branch 11 3
  let identityExpected := String.intercalate "\n" [
    "import * from std;", "import * from std.dispatch;",
    "import { div as sc_div, mod as sc_mod, shl as sc_shl, shr as sc_shr, sar as sc_sar, sdiv as sc_sdiv, smod as sc_smod, sgt as sc_sgt, addmod as sc_addmod, mulmod as sc_mulmod, clz as sc_clz, byte as sc_byte, exp as sc_exp, signextend as sc_signextend } from std.opcodes;", "",
    "contract SynthesizedPrimitives {", "    function run(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);", "        return uint256(sc_input);", "    }", "}", ""]
  ensure ((← emitted (← checked (.var 0))).source == identityExpected)
    "primitive wrapper source changed its raw aliases or runtime ABI"
  ensure (Primitive.emitterVersion == "solcore-source-primitives-v1" &&
    Primitive.wrapperVersion == "solcore-word-primitives-contract-v1" && Primitive.selector == "0xa444f5e9")
    "primitive emitter version or selector changed"

private def rejectionChecks : IO Unit := do
  ensure (unaryOps.all PrimitiveRenderer.supportedUnary &&
    binaryOps.all PrimitiveRenderer.supportedBinary && ternaryOps.all PrimitiveRenderer.supportedTernary)
    "primitive profile omitted an operation from the sealed Word/Bool catalog"
  for (body, error) in [
      (.unary .integerNot (.var 0), EmitError.unsupportedUnary .integerNot),
      (.unary .integerToWord (.var 0), .unsupportedUnary .integerToWord),
      (.unary .wordToInteger (.var 0), .unsupportedUnary .wordToInteger),
      (.binary .integerDiv (.var 0) (word 0), .unsupportedBinary .integerDiv),
      (.binary .integerEq (.var 0) (word 0), .unsupportedBinary .integerEq)] do
    ensure (!(PrimitiveRenderer.supported body)) "out-of-profile operation reported supported"
    ensure (CheckedWordFunction.ofBody? body).isNone "integer operation entered the checked Word profile"
    match PrimitiveRenderer.render .word ["sc_input"] 8 0 body with
    | .error actual => ensure (actual == error) "unsupported operation gave the wrong error"
    | .ok _ => throw (IO.userError "unsupported operation was silently substituted")
  for body in [(.var 1 : Wire.Expr), .newCell .word (word 1),
      .apply (.lambda .word .word (.var 0)) (word 1), .integer 0] do
    ensure (CheckedWordFunction.ofBody? body).isNone "primitive scope admitted a host, cell or nested function"
  match PrimitiveRenderer.render .word [] 0 0 (.var 0) with
  | .error (.unboundLocal 0) => pure ()
  | _ => throw (IO.userError "unbound printer local did not fail explicitly")
  -- Existing input-profile emission remains narrower, with unchanged behavior.
  match Input.emit (← checked (.binary .wordDiv (.var 0) (word 0))) with
  | .error (.unsupportedBinary .wordDiv) => pure ()
  | _ => throw (IO.userError "old runtime-input profile unexpectedly changed")

def testSourcePrimitiveEmitter : IO Unit := do
  ordinaryChecks
  boundaryChecks
  byteExponentChecks
  legacyScalarChecks
  formattingChecks
  rejectionChecks

end Tests.SourcePrimitiveEmitter
