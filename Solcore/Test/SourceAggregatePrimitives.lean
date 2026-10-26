import Solcore.Synthesis.Source.AggregateRenderer
import Solcore.Synthesis.Source.PrimitiveEmitter

/-! The aggregate renderer prints the raw primitive aliases with the call-graph
helpers: operand snapshots in Core order, reversed shift arguments, Boolean
conversion of signed comparison, and the original scalar spelling for the
original operations. Expected lines are hand-written goldens. -/
set_option autoImplicit false

namespace Tests.SourceAggregatePrimitives

open Solcore.Core (Word)
open Solcore.Core.Wire Solcore.Synthesis.Source

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def arg : Expr := .var 0

private def render (body : Expr) (target : Solcore.Synthesis.Core.Aggregates.Target := .word) :
    Except EmitError AggregateRenderer.Rendered :=
  AggregateRenderer.render [] target [.word "sc_arg"] 4 0 body

private def golden (name : String) (body : Expr) (lines : List String) (value : String) : IO Unit :=
  match render body with
  | .ok rendered =>
      ensure (rendered.lines == lines.map ("    " ++ ·) && rendered.value == some value)
        s!"{name} rendering changed: {rendered.lines}"
  | .error error => throw (IO.userError s!"{name} was rejected: {reprStr error}")

private def goldenChecks : IO Unit := do
  golden "addmod" (.ternary .wordAddMod arg (word 3) (word 7))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 3;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = 7;", "let sc_v4: word = sc_v3;",
      "let sc_v5: word = sc_addmod(sc_v0, sc_v2, sc_v4);"] "sc_v5"
  -- Core wordShl(value, shift) prints shl(shift, value) from the snapshots.
  golden "shl" (.binary .wordShl arg (word 8))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 8;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = sc_shl(sc_v2, sc_v0);"] "sc_v3"
  golden "sgt" (.ifE (.binary .wordSgt arg (word 1)) (word 2) (word 3))
    ["let sc_v0: word = sc_arg;", "let sc_v1: word = 1;", "let sc_v2: word = sc_v1;",
      "let sc_v3: bool = tobool(sc_sgt(sc_v0, sc_v2));", "let sc_v4: word = 0;", "if (sc_v3) {",
      "    let sc_v5: word = 2;", "    sc_v4 = sc_v5;", "} else {",
      "    let sc_v6: word = 3;", "    sc_v4 = sc_v6;", "}"] "sc_v4"
  -- A cell load is bound before Clz snapshots it; the cell itself is never passed.
  golden "clz" (.letE (.newCell .word arg) (.unary .wordClz (.loadCell (.var 0))))
    ["let sc_c0: word = sc_arg;", "let sc_v1: word = sc_c0;", "let sc_v2: word = sc_v1;",
      "let sc_v3: word = sc_clz(sc_v2);"] "sc_v3"
  -- Original operations keep their exact unsnapshotted scalar spelling.
  golden "add" (.binary .wordAdd arg (word 1))
    ["let sc_v0: word = 1;", "let sc_v1: word = (sc_arg + sc_v0);"] "sc_v1"
  golden "not" (.unary .wordNot arg) ["let sc_v0: word = (~sc_arg);"] "sc_v0"
  match render (.ternary .wordMulMod arg arg arg) .bool with
  | .error (.unsupportedExpression _) => pure ()
  | _ => throw (IO.userError "a ternary primitive was rendered at a non-Word type")
  match render (.unary .integerToWord (.integer 1)) with
  | .error (.unsupportedUnary .integerToWord) => pure ()
  | _ => throw (IO.userError "integer conversion was rendered by the aggregate renderer")

private def primitiveBodies : List Expr :=
  [.unary .wordClz arg, .ternary .wordAddMod arg (word 3) arg, .ternary .wordMulMod (word 5) arg (word 0)] ++
  ([BinaryOp.wordDiv, .wordMod, .wordShl, .wordShr, .wordSar, .wordSdiv, .wordSmod, .wordByte, .wordPow,
    .wordSignExtend].map fun operation => .binary operation arg (word 255)) ++
  [.ifE (.binary .wordSgt arg (word 1)) (.binary .wordDiv arg arg) (word 0)]

/-- On scalar bodies without Boolean lets, the aggregate renderer and the
call-graph renderer print the same text: the helpers are shared exactly. -/
private def sharedHelperChecks : IO Unit := do
  let scalarBodies := primitiveBodies ++ [.binary .wordXor (.binary .wordAdd arg (word 1)) arg,
    .letE (.ternary .wordAddMod arg arg (word 9)) (.binary .wordShr (.var 0) (.unary .wordClz (.var 1))),
    .ifE (.binary .wordGt arg (word 7)) (.unary .wordNot arg) (.binary .wordMul arg arg)]
  for body in scalarBodies do
    match render body, CallGraphRenderer.renderWithFunctions [] .word ["sc_arg"] 4 0 body with
    | .ok aggregate, .ok callGraph =>
        ensure (aggregate.lines == callGraph.lines && aggregate.value == some callGraph.value &&
          aggregate.nextId == callGraph.nextId) s!"aggregate and call-graph text differ: {aggregate.lines}"
    | _, _ => throw (IO.userError "a shared scalar body was rejected")

private def importChecks : IO Unit := do
  ensure ("import { " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++ " } from std.opcodes;" ==
    Primitive.opcodeImport) "aggregate aliases differ from the primitive profile's import"
  for body in primitiveBodies do
    ensure (AggregateRenderer.usesOpcodeAliases body) "a primitive body was not detected"
    ensure (AggregateRenderer.opcodeImports [word 0, body] == [Primitive.opcodeImport])
      "a primitive body did not import the aliases"
    -- Detection reaches operands under aggregates, cases, cells and lets.
    for nested in [Expr.pair body arg, .caseE (.inLeft .word arg) body arg, .first (.pair body arg),
        .letE (.newCell .word arg) (.storeCell (.var 0) body), .letE body arg] do
      ensure (AggregateRenderer.usesOpcodeAliases nested) "a nested primitive was not detected"
  let original := [Expr.binary .wordAdd arg (word 1), .unary .boolNot (.bool true), .unary .wordNot arg,
    .ifE (.binary .wordGt arg (word 1)) (.binary .wordSub arg arg) (.binary .wordMul arg arg)]
  ensure (original.all (! AggregateRenderer.usesOpcodeAliases ·) && AggregateRenderer.opcodeImports original == [])
    "an original-operation body imported the aliases"
  ensure (AggregateRenderer.opcodeImportWith ["sload", "sstore"] original == "import {sload, sstore} from std.opcodes;")
    "a primitive-free stateful import changed"
  ensure (AggregateRenderer.opcodeImportWith ["sload", "sstore"] (original ++ [.unary .wordClz arg]) ==
      "import {sload, sstore, " ++ ", ".intercalate AggregateRenderer.opcodeAliases ++ "} from std.opcodes;")
    "the aliases were not merged into the stateful opcode import"

def testSourceAggregatePrimitives : IO Unit := do
  goldenChecks
  sharedHelperChecks
  importChecks

end Tests.SourceAggregatePrimitives
